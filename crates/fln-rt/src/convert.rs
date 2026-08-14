//! The lazy converter membrane (plan §6.1b, R10; bead fln-lld).
//!
//! # What this is
//!
//! The ONLY membrane between the CompatHeap and the NativeHeap. A Compat
//! object graph encoding a term crosses into the NativeHeap by projection
//! (`Conversion::project_expr`); a native term crosses back by injection
//! (`inject_expr`) through the membrane's own constructors. Nothing else may
//! move a value between the two heaps — that is the acceptance's "generated
//! lazy converters are the only membrane", and the suite's tripwire cell
//! holds it at the source level.
//!
//! # The five declarations the acceptance names
//!
//! Made as data ([`PROJECT_DECL`], [`INJECT_DECL`]) so a review can diff them
//! and the suite can assert their shape:
//!
//! * **ownership** — projection takes no ownership of the Compat graph (no
//!   RC change anywhere; the graph's owners are untouched), and the native
//!   handle it returns owns nothing outside the NativeHeap. Injection
//!   allocates fresh Compat objects that own their own references.
//! * **allocation** — projection allocates native terms in the destination
//!   NativeHeap, deduplicated structurally by the terms' own computed hashes
//!   (upstream's hash-consing discipline, not pointer identity). Injection
//!   allocates through the CompatHeap membrane.
//! * **failure** — every failure is a typed [`ConvertError`], never a panic
//!   and never a fabricated term.
//! * **capability** — none. Read-only on the Compat side, allocation-only on
//!   both heaps.
//! * **no-claim** — the converter asserts STRUCTURAL FIDELITY ONLY: the
//!   projected term mirrors the Compat structure exactly (round-trip is the
//!   law). It does not assert the term is well-typed (the kernel's
//!   judgment), Reference-evaluable, or RC-preserving; those claims belong
//!   to their owners.
//!
//! # Laziness and the R10 law
//!
//! Conversion happens only on inspection: creating a [`Conversion`] and
//! dropping it without projecting allocates nothing (asserted by the
//! suite). The dual-heap memory law (R10) is served structurally: a shared
//! subgraph projects once and every later reference resolves to the same
//! handle by hash-interning, so two structurally equal inputs share one
//! native allocation rather than doubling.

#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet};

use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_unsafe_abi::handle::Obj;

use crate::abi;
use crate::native_heap::{NativeHandle, NativeHeap};

/// The converter's declaration, as data (see the module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConverterDecl {
    pub ownership: &'static str,
    pub allocation: &'static str,
    pub failure: &'static str,
    pub capability: &'static str,
    pub no_claim: &'static str,
}

/// The projection declaration (Compat -> Native).
pub const PROJECT_DECL: ConverterDecl = ConverterDecl {
    ownership: "no NET RC change: borrowed children are inc'd and released within \
                the conversion (the membrane's borrow discipline), so the graph's \
                owners observe no change; the returned native handle owns nothing \
                outside the NativeHeap",
    allocation: "allocates native terms in the destination NativeHeap, \
                 deduplicated structurally by the terms' own computed hashes",
    failure: "typed ConvertError per family, never a panic, never a fabricated term",
    capability: "none required: read-only on the Compat side, alloc-only on the Native side",
    no_claim: "structural fidelity only — not well-typedness, not \
               Reference-evaluability, not RC preservation of the source",
};

/// The injection declaration (Native -> Compat).
pub const INJECT_DECL: ConverterDecl = ConverterDecl {
    ownership: "the returned Obj owns its own references (fresh Compat objects; \
                the NativeHeap is untouched)",
    allocation: "allocates through the CompatHeap membrane constructors",
    failure: "typed ConvertError per family, never a panic, never a fabricated object",
    capability: "none required: allocation through the membrane only",
    no_claim: "structural fidelity only — the injected object mirrors the native \
               term's structure, nothing more",
};

/// Every way a conversion can fail, each typed and naming its family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvertError {
    /// The Compat structure is not the shape its family requires (a tag's
    /// field count, a string's validity, a list that ends mid-way).
    MalformedCompat {
        family: &'static str,
        reason: String,
    },
    /// A constructor outside the converted subset. The refusal names the
    /// family and the tag, so extending the subset is mechanical, and the
    /// boundary of what converts is exact rather than implicit.
    UnsupportedConstructor { family: &'static str, tag: u8 },
    /// A level or expression depth overflowed the native bound.
    NativeOverflow { family: &'static str },
}

/// Recursion ceiling kept by `enter` if a walk family grows a frame again.
/// Name, Level, and Expr projection and injection are iterative (a
/// 400-component Name and a 400-deep app nest are legal; Level.depth is
/// 24-bit). The kernel walk is 2048; 256 stayed typed (FL-INV-07) when
/// those families still recursed under a 2 MiB debug stack.
const MAX_WALK_DEPTH: u32 = 256;
/// Node visits in one conversion scope, covering iterative lists as well
/// as the recursive families.
const MAX_WALK_NODES: usize = 1_000_000;

impl std::fmt::Display for ConvertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedCompat { family, reason } => {
                write!(f, "malformed {family}: {reason}")
            }
            Self::UnsupportedConstructor { family, tag } => {
                write!(f, "unsupported {family} constructor tag {tag}")
            }
            Self::NativeOverflow { family } => {
                write!(f, "{family} overflowed the native bound")
            }
        }
    }
}

impl std::error::Error for ConvertError {}

// Compat tags, upstream's own assignments (lean.h: the object constructors
// for Name / LeanLevel / LeanLiteral / LeanExpr / List).
const TAG_NAME_ANONYMOUS: u8 = 0;
const TAG_NAME_STR: u8 = 1;
const TAG_NAME_NUM: u8 = 2;

const TAG_LEVEL_ZERO: u8 = 0;
const TAG_LEVEL_SUCC: u8 = 1;
const TAG_LEVEL_MAX: u8 = 2;
const TAG_LEVEL_IMAX: u8 = 3;
const TAG_LEVEL_PARAM: u8 = 4;
const TAG_LEVEL_MVAR: u8 = 5;

const TAG_EXPR_BVAR: u8 = 0;
const TAG_EXPR_FVAR: u8 = 1;
const TAG_EXPR_MVAR: u8 = 2;
const TAG_EXPR_SORT: u8 = 3;
const TAG_EXPR_CONST: u8 = 4;
const TAG_EXPR_APP: u8 = 5;
const TAG_EXPR_LAM: u8 = 6;
const TAG_EXPR_FORALL: u8 = 7;
const TAG_EXPR_LET: u8 = 8;
const TAG_EXPR_LIT: u8 = 9;
const TAG_EXPR_MDATA: u8 = 10;
const TAG_EXPR_PROJ: u8 = 11;

const TAG_LIT_NAT: u8 = 0;
const TAG_LIT_STR: u8 = 1;

const TAG_LIST_NIL: u8 = 0;
const TAG_LIST_CONS: u8 = 1;

const TAG_DV_STRING: u8 = 0;
const TAG_DV_BOOL: u8 = 1;
const TAG_DV_NAME: u8 = 2;
const TAG_DV_NAT: u8 = 3;
const TAG_DV_INT: u8 = 4;
const TAG_DV_SYNTAX: u8 = 5;

fn malformed(family: &'static str, reason: impl Into<String>) -> ConvertError {
    ConvertError::MalformedCompat {
        family,
        reason: reason.into(),
    }
}

/// Lean boxes a nullary constructor as `lean_box(ctorIdx)`. `Name.anonymous`,
/// `Level.zero`, and `List.nil` are all ctor 0, so they share the small-Nat
/// 0 bit pattern. Convert's own inject still uses a 0-field heap ctor;
/// projection must accept both, or a Lean-true graph is refused as malformed.
fn lean_box0(obj: &Obj) -> bool {
    obj.is_scalar() && obj.unbox() == 0
}

/// `ctor_child` asserts arity. Convert's public project path promised a
/// typed `ConvertError` and never a panic, so a short constructor is a
/// malformed graph, not an invariant failure.
fn ctor_field(obj: &Obj, i: usize, family: &'static str) -> Result<Obj, ConvertError> {
    if obj.is_scalar() {
        return Err(malformed(
            family,
            "a tagged scalar has no constructor fields",
        ));
    }
    let header = obj.header();
    if header.tag > abi::TAG_MAX_CTOR_TAG {
        return Err(malformed(family, "not a constructor object"));
    }
    if i >= usize::from(header.other) {
        return Err(malformed(
            family,
            format!("constructor has {} fields, needed field {i}", header.other),
        ));
    }
    Ok(obj.ctor_child(i))
}

/// `ctor_scalar_u64` asserts the offset is inside the scalar area. A missing
/// bvar index or Name.num component is a malformed graph, not an abort.
fn ctor_u64(obj: &Obj, byte_off: usize, family: &'static str) -> Result<u64, ConvertError> {
    if obj.is_scalar() {
        return Err(malformed(family, "a tagged scalar has no scalar area"));
    }
    let header = obj.header();
    if header.tag > abi::TAG_MAX_CTOR_TAG {
        return Err(malformed(family, "not a constructor object"));
    }
    let floor = usize::from(header.other) * 8;
    let extent = usize::from(header.cs_sz).saturating_sub(8);
    if byte_off < floor || byte_off + 8 > extent {
        return Err(malformed(family, "constructor scalar is missing"));
    }
    Ok(obj.ctor_scalar_u64(byte_off))
}

/// A Lean `Nat` object: tagged scalar or nonnegative mpz. Wider than `u64`
/// cannot enter `Name::num` or a `u32` bvar index.
fn nat_u64(obj: &Obj, family: &'static str) -> Result<u64, ConvertError> {
    if obj.is_scalar() {
        return Ok(obj.unbox() as u64);
    }
    if obj.obj_tag() != usize::from(abi::TAG_MPZ) {
        return Err(malformed(family, "expected a Nat (scalar or mpz)"));
    }
    let Some((_, size, limbs)) = obj.try_mpz_view() else {
        return Err(malformed(family, "mpz header is inconsistent"));
    };
    if size < 0 {
        return Err(malformed(family, "a natural number is negative"));
    }
    match limbs {
        [] => Ok(0),
        [limb] => Ok(*limb),
        _ => Err(malformed(family, "Nat exceeds u64")),
    }
}

/// Lean `Int`: a tagged scalar whose payload is a sign-extended `i32`
/// (olean `decode_int` on 64-bit: `(ptr >> 1) as u32 as i32`), or a
/// nonnegative/negative mpz whose live magnitude fits `i64`.
fn int_i64(obj: &Obj, family: &'static str) -> Result<i64, ConvertError> {
    if obj.is_scalar() {
        return Ok(i64::from(obj.unbox() as u32 as i32));
    }
    if obj.obj_tag() != usize::from(abi::TAG_MPZ) {
        return Err(malformed(family, "expected an Int (scalar or mpz)"));
    }
    let Some((_, size, limbs)) = obj.try_mpz_view() else {
        return Err(malformed(family, "mpz header is inconsistent"));
    };
    let negative = size < 0;
    match limbs {
        [] => Ok(0),
        [limb] if negative && *limb == 1u64 << 63 => Ok(i64::MIN),
        [limb] if negative => {
            let magnitude =
                i64::try_from(*limb).map_err(|_| malformed(family, "Int exceeds i64"))?;
            Ok(-magnitude)
        }
        [limb] => i64::try_from(*limb).map_err(|_| malformed(family, "Int exceeds i64")),
        _ => Err(malformed(family, "Int exceeds i64")),
    }
}

/// First scalar `u8` after the leading Data word. Lean packs `BinderInfo`
/// and `letE.nonDep` there; small-object alignment zero-pads the rest of
/// the word, so a `u64` read is the safe API and the low byte is the value.
fn ctor_u8_after_data(obj: &Obj, family: &'static str) -> Result<u8, ConvertError> {
    let byte_off = usize::from(obj.header().other) * 8 + 8;
    Ok(ctor_u64(obj, byte_off, family)? as u8)
}

fn binder_info_of(obj: &Obj) -> Result<BinderInfo, ConvertError> {
    match ctor_u8_after_data(obj, "expr")? {
        0 => Ok(BinderInfo::Default),
        1 => Ok(BinderInfo::Implicit),
        2 => Ok(BinderInfo::StrictImplicit),
        3 => Ok(BinderInfo::InstImplicit),
        _ => Err(malformed("expr", "BinderInfo byte is not 0..=3")),
    }
}

fn bool_after_data(obj: &Obj, family: &'static str) -> Result<bool, ConvertError> {
    match ctor_u8_after_data(obj, family)? {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(malformed(family, "noncanonical Bool")),
    }
}

fn data_and_u8(data: u64, extra: u8) -> Vec<u8> {
    let mut bytes = data.to_le_bytes().to_vec();
    bytes.push(extra);
    bytes
}

/// Lean-true object-slot count for an Expr constructor. `None` is an
/// unknown tag. A constructor whose `other` differs is the older
/// convert-subset packing (inline bvar index, …) and has no Data word.
fn expr_lean_slots(tag: u8) -> Option<u8> {
    Some(match tag {
        TAG_EXPR_BVAR | TAG_EXPR_FVAR | TAG_EXPR_MVAR | TAG_EXPR_SORT | TAG_EXPR_LIT => 1,
        TAG_EXPR_CONST | TAG_EXPR_APP | TAG_EXPR_MDATA => 2,
        TAG_EXPR_LAM | TAG_EXPR_FORALL | TAG_EXPR_PROJ => 3,
        TAG_EXPR_LET => 4,
        _ => return None,
    })
}

fn level_lean_slots(tag: u8) -> Option<u8> {
    Some(match tag {
        TAG_LEVEL_SUCC | TAG_LEVEL_PARAM | TAG_LEVEL_MVAR => 1,
        TAG_LEVEL_MAX | TAG_LEVEL_IMAX => 2,
        _ => return None,
    })
}

/// First scalar u64 after the Lean-true children, when that word is present.
/// Missing bytes stay `None` so children-only objects still project.
fn stored_data_word(obj: &Obj, slots: Option<u8>, family: &'static str) -> Option<u64> {
    let slots = slots?;
    if obj.is_scalar() || obj.header().other != slots {
        return None;
    }
    ctor_u64(obj, usize::from(slots) * 8, family).ok()
}

fn expr_from_done(done: &HashMap<usize, Expr>, obj: &Obj, i: usize) -> Result<Expr, ConvertError> {
    let child = ctor_field(obj, i, "expr")?;
    done.get(&child.identity_token())
        .cloned()
        .ok_or_else(|| malformed("expr", "child was not projected before its parent"))
}

fn check_expr_data(obj: &Obj, expr: &Expr) -> Result<(), ConvertError> {
    let Some(stored) = stored_data_word(obj, expr_lean_slots(obj.obj_tag() as u8), "expr") else {
        return Ok(());
    };
    if stored != expr.data().0 {
        return Err(malformed(
            "expr",
            "stored Expr.Data does not match the children",
        ));
    }
    Ok(())
}

fn check_name_hash(obj: &Obj, name: &Name) -> Result<(), ConvertError> {
    // Lean Name.str / Name.num are two object children plus the cached hash.
    // The older one-child Name.num packing stores the component at offset 8,
    // not a hash; children-only Name.str objects have no hash word.
    if obj.is_scalar() || obj.header().other != 2 {
        return Ok(());
    }
    let Ok(stored) = ctor_u64(obj, 16, "name") else {
        return Ok(());
    };
    if stored != name.hash() {
        return Err(malformed(
            "name",
            "stored Name.hash does not match the children",
        ));
    }
    Ok(())
}

fn check_level_data(obj: &Obj, level: &Level) -> Result<(), ConvertError> {
    let Some(stored) = stored_data_word(obj, level_lean_slots(obj.obj_tag() as u8), "level") else {
        return Ok(());
    };
    if stored != level.data().0 {
        return Err(malformed(
            "level",
            "stored Level.Data does not match the children",
        ));
    }
    Ok(())
}

/// A conversion scope: the accounting for one lazy boundary crossing.
/// Creating one is free; dropping it without projecting allocates nothing.
/// The dedup itself lives in the destination heap's interning, so the
/// accounting is the whole region state — R10's short-lived conversion
/// region, with nothing left behind when it ends.
#[derive(Debug, Default)]
pub struct Conversion {
    projected: usize,
    dedup_hits: usize,
    depth: u32,
    nodes: usize,
}

impl Conversion {
    pub fn new() -> Self {
        Self::default()
    }

    /// Terms projected in this scope (before interning dedup).
    pub fn projected(&self) -> usize {
        self.projected
    }

    /// Projections that resolved to an already-interned handle (the R10
    /// count: this many native allocations did NOT happen).
    pub fn dedup_hits(&self) -> usize {
        self.dedup_hits
    }

    /// End the scope, returning the accounting. Nothing survives it: the
    /// dedup state is the destination heap's intern index, which is the
    /// heap's own property, not the conversion's.
    pub fn finish(self) -> (usize, usize) {
        (self.projected, self.dedup_hits)
    }

    fn enter(&mut self, family: &'static str) -> Result<(), ConvertError> {
        self.nodes = self.nodes.saturating_add(1);
        if self.nodes > MAX_WALK_NODES {
            return Err(malformed(family, "conversion walk exceeded the node bound"));
        }
        if self.depth >= MAX_WALK_DEPTH {
            return Err(ConvertError::NativeOverflow { family });
        }
        Ok(())
    }

    fn expr(&mut self, obj: &Obj) -> Result<Expr, ConvertError> {
        self.project_expr_graph(obj)
    }

    fn name(&mut self, obj: &Obj) -> Result<Name, ConvertError> {
        self.project_name(obj)
    }

    fn level(&mut self, obj: &Obj) -> Result<Level, ConvertError> {
        self.project_level(obj)
    }

    /// Project a Compat Expr graph into the NativeHeap, deduplicated by the
    /// terms' own computed hashes (upstream's hash-consing discipline).
    pub fn project_expr(
        &mut self,
        heap: &mut NativeHeap,
        root: &Obj,
    ) -> Result<NativeHandle<Expr>, ConvertError> {
        self.projected += 1;
        let before = heap.live();
        let handle = heap.intern_by(
            self.expr(root)?,
            |e: &Expr| e.hash(),
            |a: &Expr, b: &Expr| a.hash() == b.hash(),
        );
        if heap.live() == before {
            self.dedup_hits += 1;
        }
        Ok(handle)
    }

    fn project_expr_graph(&mut self, root: &Obj) -> Result<Expr, ConvertError> {
        // Iterative post-order: a 400-deep app nest is a legal native
        // value, and the recursive form overflowed at the host-stack
        // ceiling that still bounds inject (FL-INV-07).
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut stack = vec![root.clone_ref()];
        while let Some(current) = stack.last().map(Obj::clone_ref) {
            if current.is_scalar() {
                return Err(malformed(
                    "expr",
                    "a bare tagged scalar is not an expression object",
                ));
            }
            let key = current.identity_token();
            if done.contains_key(&key) {
                stack.pop();
                continue;
            }
            let tag = current.obj_tag() as u8;
            let child_slots: &[usize] = match tag {
                TAG_EXPR_APP => &[0, 1],
                TAG_EXPR_LAM | TAG_EXPR_FORALL => &[1, 2],
                TAG_EXPR_LET => &[1, 2, 3],
                TAG_EXPR_MDATA => &[1],
                TAG_EXPR_PROJ => &[2],
                TAG_EXPR_BVAR | TAG_EXPR_FVAR | TAG_EXPR_MVAR | TAG_EXPR_SORT | TAG_EXPR_CONST
                | TAG_EXPR_LIT => &[],
                other => {
                    return Err(ConvertError::UnsupportedConstructor {
                        family: "expr",
                        tag: other,
                    });
                }
            };
            let mut pending = false;
            let ancestors = stack.len();
            for &i in child_slots {
                let child = ctor_field(&current, i, "expr")?;
                if child.is_scalar() {
                    return Err(malformed(
                        "expr",
                        "a bare tagged scalar is not an expression object",
                    ));
                }
                let child_key = child.identity_token();
                if done.contains_key(&child_key) {
                    continue;
                }
                if stack[..ancestors]
                    .iter()
                    .any(|frame| frame.identity_token() == child_key)
                {
                    return Err(malformed("expr", "expr graph is cyclic"));
                }
                stack.push(child);
                pending = true;
            }
            if pending {
                continue;
            }
            self.enter("expr")?;
            let current = stack.pop().expect("the parent is still on the stack");
            let projected = self.project_expr_node(&current, &done)?;
            check_expr_data(&current, &projected)?;
            done.insert(key, projected);
        }
        done.get(&root.identity_token())
            .cloned()
            .ok_or_else(|| malformed("expr", "expr was not projected"))
    }

    fn project_expr_node(
        &mut self,
        obj: &Obj,
        done: &HashMap<usize, Expr>,
    ) -> Result<Expr, ConvertError> {
        let tag = obj.obj_tag() as u8;
        match tag {
            TAG_EXPR_BVAR => {
                // Lean `bvar` is one Nat child. Convert's own inject stores
                // an inline u64 with `other == 0`. Both packings are live.
                // Truncating with `as u32` turns `2^32 + 5` into `bvar(5)` —
                // a fabricated term. `NativeOverflow` is the family the
                // range covenant already uses when the index is merely too
                // wide for `Expr::bvar`.
                let index = if obj.header().other >= 1 {
                    nat_u64(&ctor_field(obj, 0, "expr")?, "expr")?
                } else {
                    ctor_u64(obj, 0, "expr")?
                };
                let index = u32::try_from(index)
                    .map_err(|_| ConvertError::NativeOverflow { family: "expr" })?;
                Expr::bvar(index).map_err(|_| ConvertError::NativeOverflow { family: "expr" })
            }
            TAG_EXPR_FVAR => {
                let name = self.name(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::fvar(fln_core::expr::FVarId(name)))
            }
            TAG_EXPR_MVAR => {
                let name = self.name(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::mvar(MVarId(name)))
            }
            TAG_EXPR_SORT => {
                let level = self.level(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::sort(level))
            }
            TAG_EXPR_CONST => {
                let name = self.name(&ctor_field(obj, 0, "expr")?)?;
                let levels = self.level_list(&ctor_field(obj, 1, "expr")?)?;
                Ok(Expr::const_(name, levels))
            }
            TAG_EXPR_APP => Ok(Expr::app(
                expr_from_done(done, obj, 0)?,
                expr_from_done(done, obj, 1)?,
            )),
            TAG_EXPR_LAM => {
                let binder_name = self.name(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::lam(
                    binder_name,
                    expr_from_done(done, obj, 1)?,
                    expr_from_done(done, obj, 2)?,
                    binder_info_of(obj)?,
                ))
            }
            TAG_EXPR_FORALL => {
                let binder_name = self.name(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::forall_e(
                    binder_name,
                    expr_from_done(done, obj, 1)?,
                    expr_from_done(done, obj, 2)?,
                    binder_info_of(obj)?,
                ))
            }
            TAG_EXPR_LET => {
                let decl_name = self.name(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::let_e(
                    decl_name,
                    expr_from_done(done, obj, 1)?,
                    expr_from_done(done, obj, 2)?,
                    expr_from_done(done, obj, 3)?,
                    bool_after_data(obj, "expr")?,
                ))
            }
            TAG_EXPR_LIT => {
                let literal = self.literal(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::lit(literal))
            }
            TAG_EXPR_MDATA => {
                let data = self.kvmap(&ctor_field(obj, 0, "expr")?)?;
                Ok(Expr::mdata(data, expr_from_done(done, obj, 1)?))
            }
            TAG_EXPR_PROJ => {
                let struct_name = self.name(&ctor_field(obj, 0, "expr")?)?;
                let idx = nat_u64(&ctor_field(obj, 1, "expr")?, "expr")?;
                Ok(Expr::proj(struct_name, idx, expr_from_done(done, obj, 2)?))
            }
            other => Err(ConvertError::UnsupportedConstructor {
                family: "expr",
                tag: other,
            }),
        }
    }

    fn project_name(&mut self, root: &Obj) -> Result<Name, ConvertError> {
        // Iterative on the parent chain: a 400-component Name is a legal
        // native value, and the recursive form overflowed at the host-stack
        // ceiling that still bounds inject (FL-INV-07).
        let mut chain = Vec::new();
        let mut cursor = root.clone_ref();
        let mut seen = HashSet::new();
        loop {
            self.enter("name")?;
            if lean_box0(&cursor) {
                break;
            }
            if cursor.is_scalar() {
                return Err(malformed("name", "a tagged scalar is not a name object"));
            }
            if !seen.insert(cursor.identity_token()) {
                return Err(malformed("name", "name graph is cyclic"));
            }
            match cursor.obj_tag() as u8 {
                TAG_NAME_ANONYMOUS => break,
                TAG_NAME_STR | TAG_NAME_NUM => {
                    chain.push(cursor.clone_ref());
                    cursor = ctor_field(&cursor, 0, "name")?;
                }
                other => {
                    return Err(ConvertError::UnsupportedConstructor {
                        family: "name",
                        tag: other,
                    });
                }
            }
        }
        let mut name = Name::anonymous();
        for obj in chain.into_iter().rev() {
            name = match obj.obj_tag() as u8 {
                TAG_NAME_STR => {
                    let text = self.string(&ctor_field(&obj, 1, "name")?)?;
                    Name::str(name, text)
                }
                TAG_NAME_NUM => {
                    let header = obj.header();
                    let component = if header.other >= 2 {
                        // Lean: (pre : Name) (i : Nat) plus a cached hash scalar.
                        nat_u64(&ctor_field(&obj, 1, "name")?, "name")?
                    } else {
                        // Convert subset: one child plus an inline u64. Offset 0
                        // is the parent pointer; `ctor_scalar_u64` measures from
                        // obj_cptr and requires `offset >= other * 8`.
                        ctor_u64(&obj, 8, "name")?
                    };
                    Name::num(name, component)
                }
                _ => unreachable!("only str/num were chained"),
            };
            check_name_hash(&obj, &name)?;
        }
        Ok(name)
    }

    fn project_level(&mut self, root: &Obj) -> Result<Level, ConvertError> {
        // Iterative post-order, keyed by identity_token: Level.depth is
        // 24-bit, so a succ tower can legally exceed the 256-frame host
        // stack that still bounds the recursive expr/name projectors.
        // A child already on the stack is a cycle in the Compat graph.
        let mut done: HashMap<usize, Level> = HashMap::new();
        let mut stack = vec![root.clone_ref()];
        while let Some(current) = stack.last().map(Obj::clone_ref) {
            let key = current.identity_token();
            if lean_box0(&current) {
                self.enter("level")?;
                done.insert(key, Level::zero());
                stack.pop();
                continue;
            }
            if done.contains_key(&key) {
                stack.pop();
                continue;
            }
            if current.is_scalar() {
                return Err(malformed("level", "a tagged scalar is not a level object"));
            }
            let tag = current.obj_tag() as u8;
            let child_slots: &[usize] = match tag {
                TAG_LEVEL_ZERO => &[],
                TAG_LEVEL_SUCC => &[0],
                TAG_LEVEL_MAX | TAG_LEVEL_IMAX => &[0, 1],
                TAG_LEVEL_PARAM | TAG_LEVEL_MVAR => &[],
                other => {
                    return Err(ConvertError::UnsupportedConstructor {
                        family: "level",
                        tag: other,
                    });
                }
            };
            let mut pending = false;
            // Only ancestors are a cycle. A sibling already pushed this
            // visit (max of a shared child) is the same work item twice.
            let ancestors = stack.len();
            for &i in child_slots {
                let child = ctor_field(&current, i, "level")?;
                let child_key = child.identity_token();
                if lean_box0(&child) {
                    if let std::collections::hash_map::Entry::Vacant(slot) = done.entry(child_key) {
                        self.enter("level")?;
                        slot.insert(Level::zero());
                    }
                    continue;
                }
                if done.contains_key(&child_key) {
                    continue;
                }
                if stack[..ancestors]
                    .iter()
                    .any(|frame| frame.identity_token() == child_key)
                {
                    return Err(malformed("level", "level graph is cyclic"));
                }
                stack.push(child);
                pending = true;
            }
            if pending {
                continue;
            }
            self.enter("level")?;
            let current = stack.pop().expect("the parent is still on the stack");
            let projected = match tag {
                TAG_LEVEL_ZERO => Level::zero(),
                TAG_LEVEL_SUCC => {
                    let child = ctor_field(&current, 0, "level")?;
                    let inner = done.get(&child.identity_token()).ok_or_else(|| {
                        malformed("level", "succ child was not projected before its parent")
                    })?;
                    inner
                        .clone()
                        .succ()
                        .map_err(|_| ConvertError::NativeOverflow { family: "level" })?
                }
                TAG_LEVEL_MAX => {
                    let a = ctor_field(&current, 0, "level")?;
                    let b = ctor_field(&current, 1, "level")?;
                    let left = done.get(&a.identity_token()).ok_or_else(|| {
                        malformed("level", "max left was not projected before its parent")
                    })?;
                    let right = done.get(&b.identity_token()).ok_or_else(|| {
                        malformed("level", "max right was not projected before its parent")
                    })?;
                    Level::max(left.clone(), right.clone())
                        .map_err(|_| ConvertError::NativeOverflow { family: "level" })?
                }
                TAG_LEVEL_IMAX => {
                    let a = ctor_field(&current, 0, "level")?;
                    let b = ctor_field(&current, 1, "level")?;
                    let left = done.get(&a.identity_token()).ok_or_else(|| {
                        malformed("level", "imax left was not projected before its parent")
                    })?;
                    let right = done.get(&b.identity_token()).ok_or_else(|| {
                        malformed("level", "imax right was not projected before its parent")
                    })?;
                    Level::imax(left.clone(), right.clone())
                        .map_err(|_| ConvertError::NativeOverflow { family: "level" })?
                }
                TAG_LEVEL_PARAM => {
                    let name = self.name(&ctor_field(&current, 0, "level")?)?;
                    Level::param(name)
                }
                TAG_LEVEL_MVAR => {
                    let name = self.name(&ctor_field(&current, 0, "level")?)?;
                    Level::mvar(LMVarId(name))
                }
                _ => unreachable!("tag classified above"),
            };
            check_level_data(&current, &projected)?;
            done.insert(key, projected);
        }
        done.get(&root.identity_token())
            .cloned()
            .ok_or_else(|| malformed("level", "level was not projected"))
    }

    fn literal(&mut self, obj: &Obj) -> Result<Literal, ConvertError> {
        if obj.is_scalar() {
            return Err(malformed(
                "literal",
                "a tagged scalar is not a literal object",
            ));
        }
        match obj.obj_tag() as u8 {
            TAG_LIT_NAT => {
                let payload = ctor_field(obj, 0, "literal")?;
                if payload.is_scalar() {
                    Ok(Literal::Nat(NatLit::from_u64(payload.unbox() as u64)))
                } else if payload.obj_tag() != usize::from(abi::TAG_MPZ) {
                    // `mpz_view` asserts the mpz tag. A string or ctor
                    // payload is a malformed Nat, not an invariant failure.
                    Err(malformed(
                        "literal",
                        "a non-scalar Nat payload must be an mpz object",
                    ))
                } else {
                    let Some((_alloc, size, limbs)) = payload.try_mpz_view() else {
                        return Err(malformed("literal", "mpz header is inconsistent"));
                    };
                    // `try_mpz_view` is `(alloc, size, limbs)`. `alloc` is
                    // always non-negative; the sign lives in `size`.
                    if size < 0 {
                        return Err(malformed("literal", "a natural literal is negative"));
                    }
                    let live = usize::try_from(size).map_err(|_| {
                        malformed("literal", "mpz size field exceeds the limb span")
                    })?;
                    if live > limbs.len() {
                        return Err(malformed("literal", "mpz size field exceeds the limb span"));
                    }
                    Ok(Literal::Nat(NatLit::from_limbs_le(limbs[..live].to_vec())))
                }
            }
            TAG_LIT_STR => {
                let text = self.string(&ctor_field(obj, 0, "literal")?)?;
                Ok(Literal::Str(text))
            }
            other => Err(ConvertError::UnsupportedConstructor {
                family: "literal",
                tag: other,
            }),
        }
    }

    fn level_list(&mut self, obj: &Obj) -> Result<Vec<Level>, ConvertError> {
        let mut out = Vec::new();
        let mut cursor = obj.clone_ref();
        loop {
            self.enter("level-list")?;
            if lean_box0(&cursor) {
                return Ok(out);
            }
            if cursor.is_scalar() {
                return Err(malformed("level-list", "the list ends in a scalar"));
            }
            match cursor.obj_tag() as u8 {
                TAG_LIST_NIL => return Ok(out),
                TAG_LIST_CONS => {
                    out.push(self.level(&ctor_field(&cursor, 0, "level-list")?)?);
                    cursor = ctor_field(&cursor, 1, "level-list")?;
                }
                other => {
                    return Err(ConvertError::UnsupportedConstructor {
                        family: "level-list",
                        tag: other,
                    });
                }
            }
        }
    }

    fn kvmap(&mut self, obj: &Obj) -> Result<KVMap, ConvertError> {
        // KVMap is a structure erased to its entry list. Duplicate keys are
        // legal and preserved (the pin's `from_entries` / `KVMap.mk`).
        let mut entries = Vec::new();
        let mut cursor = obj.clone_ref();
        loop {
            self.enter("kvmap")?;
            if lean_box0(&cursor) {
                return Ok(KVMap::from_entries(entries));
            }
            if cursor.is_scalar() {
                return Err(malformed("kvmap", "the list ends in a scalar"));
            }
            match cursor.obj_tag() as u8 {
                TAG_LIST_NIL => return Ok(KVMap::from_entries(entries)),
                TAG_LIST_CONS => {
                    let pair = ctor_field(&cursor, 0, "kvmap")?;
                    if pair.is_scalar() || pair.obj_tag() as u8 != 0 || pair.header().other != 2 {
                        return Err(malformed("kvmap", "expected a Name × DataValue pair"));
                    }
                    let key = self.name(&ctor_field(&pair, 0, "kvmap")?)?;
                    let value = self.data_value(&ctor_field(&pair, 1, "kvmap")?)?;
                    entries.push((key, value));
                    cursor = ctor_field(&cursor, 1, "kvmap")?;
                }
                other => {
                    return Err(ConvertError::UnsupportedConstructor {
                        family: "kvmap",
                        tag: other,
                    });
                }
            }
        }
    }

    fn data_value(&mut self, obj: &Obj) -> Result<DataValue, ConvertError> {
        if obj.is_scalar() {
            return Err(malformed(
                "data-value",
                "a tagged scalar is not a DataValue object",
            ));
        }
        match obj.obj_tag() as u8 {
            TAG_DV_STRING => {
                let text = self.string(&ctor_field(obj, 0, "data-value")?)?;
                Ok(DataValue::OfString(text))
            }
            TAG_DV_BOOL => {
                if obj.header().other != 0 {
                    return Err(malformed("data-value", "ofBool has no object fields"));
                }
                match ctor_u64(obj, 0, "data-value")? as u8 {
                    0 => Ok(DataValue::OfBool(false)),
                    1 => Ok(DataValue::OfBool(true)),
                    _ => Err(malformed("data-value", "noncanonical Bool")),
                }
            }
            TAG_DV_NAME => {
                let name = self.name(&ctor_field(obj, 0, "data-value")?)?;
                Ok(DataValue::OfName(name))
            }
            TAG_DV_NAT => {
                let n = nat_u64(&ctor_field(obj, 0, "data-value")?, "data-value")?;
                Ok(DataValue::OfNat(n))
            }
            TAG_DV_INT => {
                let value = int_i64(&ctor_field(obj, 0, "data-value")?, "data-value")?;
                Ok(DataValue::OfInt(value))
            }
            TAG_DV_SYNTAX => {
                // Olean stores a scalar-or-offset handle when the payload is
                // not a live Syntax tree. A constructor child is a real
                // Syntax object; this membrane has no arena, so that stays
                // a typed subset refusal rather than a fabricated handle.
                let payload = ctor_field(obj, 0, "data-value")?;
                if payload.is_scalar()
                    || (!payload.is_scalar() && payload.obj_tag() == usize::from(abi::TAG_MPZ))
                {
                    Ok(DataValue::OfSyntax(SyntaxHandle(nat_u64(
                        &payload,
                        "data-value",
                    )?)))
                } else {
                    Err(ConvertError::UnsupportedConstructor {
                        family: "data-value",
                        tag: TAG_DV_SYNTAX,
                    })
                }
            }
            other => Err(ConvertError::UnsupportedConstructor {
                family: "data-value",
                tag: other,
            }),
        }
    }

    fn string(&mut self, obj: &Obj) -> Result<String, ConvertError> {
        if obj.is_scalar() {
            return Err(malformed(
                "string",
                "a tagged scalar is not a string object",
            ));
        }
        if obj.obj_tag() != usize::from(abi::TAG_STRING) {
            // `try_string_view` refuses a non-string. Name.str's second
            // child being a ctor is a malformed name, not a panic.
            return Err(malformed("string", "expected a string object"));
        }
        // `try_string_view` is `(m_size, m_capacity, m_length, bytes-with-NUL)`.
        // `m_length` is the UTF-8 scalar count, the same field
        // `lean_string_length` boxes. Slicing the buffer with it treats
        // "héllo" (5 scalars, 6 payload bytes) as a 5-byte string and
        // silently drops the last character — or splits a multi-byte
        // scalar and fails UTF-8. The payload is `m_size - 1` bytes.
        // Header laws (`m_size == 0`, `m_size > m_capacity`, missing NUL)
        // are refused before the copy; the checks below are the payload
        // laws that still need the bytes in hand.
        let Some((size, _, length, bytes)) = obj.try_string_view() else {
            return Err(malformed("string", "hostile or inconsistent string header"));
        };
        let content = std::str::from_utf8(&bytes[..size - 1])
            .map_err(|_| malformed("string", "invalid UTF-8"))?;
        if content.chars().count() != length {
            return Err(malformed(
                "string",
                "m_length is not the UTF-8 scalar count",
            ));
        }
        Ok(content.to_owned())
    }
}

/// Inject a native Expr back into fresh Compat objects (the injection
/// declaration: the result owns its own references; the heap is untouched).
pub fn inject_expr(heap: &NativeHeap, handle: NativeHandle<Expr>) -> Result<Obj, ConvertError> {
    let expr = heap
        .get(handle)
        .map_err(|_| malformed("expr", "the native handle does not resolve"))?;
    inject_expr_value(expr)
}

fn inject_expr_value(expr: &Expr) -> Result<Obj, ConvertError> {
    // Iterative post-order: a 400-deep app nest is a legal native value,
    // and the recursive form overflowed at the host-stack ceiling that
    // used to bound every convert walk (FL-INV-07). Native Exprs are
    // acyclic, so the memo is sharing, not cycle detection.
    let mut done: HashMap<Expr, Obj> = HashMap::new();
    let mut stack = vec![(expr.clone(), false)];
    while let Some((current, exit)) = stack.pop() {
        if done.contains_key(&current) {
            continue;
        }
        if !exit {
            stack.push((current.clone(), true));
            match current.node() {
                ExprNode::App { f, a } => {
                    stack.push((a.clone(), false));
                    stack.push((f.clone(), false));
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    stack.push((body.clone(), false));
                    stack.push((binder_type.clone(), false));
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    stack.push((body.clone(), false));
                    stack.push((value.clone(), false));
                    stack.push((type_.clone(), false));
                }
                ExprNode::MData { expr: inner, .. } | ExprNode::Proj { expr: inner, .. } => {
                    stack.push((inner.clone(), false));
                }
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Const { .. }
                | ExprNode::Lit { .. } => {}
            }
            continue;
        }
        let data_bytes = current.data().0.to_le_bytes();
        let object = match current.node() {
            ExprNode::BVar { idx } => Obj::mk_ctor(
                TAG_EXPR_BVAR,
                vec![inject_nat(u64::from(*idx))],
                &data_bytes,
            ),
            ExprNode::FVar { id } => {
                Obj::mk_ctor(TAG_EXPR_FVAR, vec![inject_name(&id.0)], &data_bytes)
            }
            ExprNode::Sort { level } => {
                Obj::mk_ctor(TAG_EXPR_SORT, vec![inject_level(level)?], &data_bytes)
            }
            ExprNode::Const { name, levels } => Obj::mk_ctor(
                TAG_EXPR_CONST,
                vec![inject_name(name), inject_level_list(levels)?],
                &data_bytes,
            ),
            ExprNode::App { f, a } => {
                let left = done
                    .get(f)
                    .ok_or_else(|| malformed("expr", "app function was not encoded"))?;
                let right = done
                    .get(a)
                    .ok_or_else(|| malformed("expr", "app argument was not encoded"))?;
                Obj::mk_ctor(
                    TAG_EXPR_APP,
                    vec![left.clone_ref(), right.clone_ref()],
                    &data_bytes,
                )
            }
            ExprNode::Lit { literal } => {
                Obj::mk_ctor(TAG_EXPR_LIT, vec![inject_literal(literal)], &data_bytes)
            }
            ExprNode::MVar { id } => {
                Obj::mk_ctor(TAG_EXPR_MVAR, vec![inject_name(&id.0)], &data_bytes)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let ty = done
                    .get(binder_type)
                    .ok_or_else(|| malformed("expr", "lam binder type was not encoded"))?;
                let inner = done
                    .get(body)
                    .ok_or_else(|| malformed("expr", "lam body was not encoded"))?;
                Obj::mk_ctor(
                    TAG_EXPR_LAM,
                    vec![inject_name(binder_name), ty.clone_ref(), inner.clone_ref()],
                    &data_and_u8(current.data().0, binder_info.to_u64() as u8),
                )
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let ty = done
                    .get(binder_type)
                    .ok_or_else(|| malformed("expr", "forall binder type was not encoded"))?;
                let inner = done
                    .get(body)
                    .ok_or_else(|| malformed("expr", "forall body was not encoded"))?;
                Obj::mk_ctor(
                    TAG_EXPR_FORALL,
                    vec![inject_name(binder_name), ty.clone_ref(), inner.clone_ref()],
                    &data_and_u8(current.data().0, binder_info.to_u64() as u8),
                )
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                let ty = done
                    .get(type_)
                    .ok_or_else(|| malformed("expr", "let type was not encoded"))?;
                let val = done
                    .get(value)
                    .ok_or_else(|| malformed("expr", "let value was not encoded"))?;
                let inner = done
                    .get(body)
                    .ok_or_else(|| malformed("expr", "let body was not encoded"))?;
                Obj::mk_ctor(
                    TAG_EXPR_LET,
                    vec![
                        inject_name(decl_name),
                        ty.clone_ref(),
                        val.clone_ref(),
                        inner.clone_ref(),
                    ],
                    &data_and_u8(current.data().0, u8::from(*non_dep)),
                )
            }
            ExprNode::MData { data, expr: inner } => {
                let child = done
                    .get(inner)
                    .ok_or_else(|| malformed("expr", "mdata child was not encoded"))?;
                Obj::mk_ctor(
                    TAG_EXPR_MDATA,
                    vec![inject_kvmap(data)?, child.clone_ref()],
                    &data_bytes,
                )
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr: inner,
            } => {
                let child = done
                    .get(inner)
                    .ok_or_else(|| malformed("expr", "proj child was not encoded"))?;
                Obj::mk_ctor(
                    TAG_EXPR_PROJ,
                    vec![
                        inject_name(struct_name),
                        inject_nat(*idx),
                        child.clone_ref(),
                    ],
                    &data_bytes,
                )
            }
        };
        done.insert(current, object);
    }
    done.get(expr)
        .map(Obj::clone_ref)
        .ok_or_else(|| malformed("expr", "expr was not encoded"))
}

fn inject_name(name: &Name) -> Obj {
    // Iterative on the parent chain: a 400-component Name is a legal
    // native value, and the recursive form blew the host stack the same
    // way the pre-bound projector did (FL-INV-07).
    if name.is_anonymous() {
        // Lean boxes a 0-field ctor as `lean_box(0)`. Olean write uses
        // the same encoding; a heap ctor tag 0 is convert-private and
        // would not survive a Lean-true Name walk.
        return Obj::mk_nat(0);
    }
    let mut chain = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        chain.push(cursor.clone());
        cursor = cursor.parent();
    }
    let mut current = Obj::mk_nat(0);
    for component in chain.into_iter().rev() {
        current = match component.leaf_view() {
            fln_core::name::LeafView::Str(text) => Obj::mk_ctor(
                TAG_NAME_STR,
                vec![current, Obj::mk_string(text)],
                &component.hash().to_le_bytes(),
            ),
            fln_core::name::LeafView::Num(component_num) => Obj::mk_ctor(
                TAG_NAME_NUM,
                vec![current, inject_nat(component_num)],
                &component.hash().to_le_bytes(),
            ),
            fln_core::name::LeafView::Anonymous => {
                unreachable!("parent is anonymous but leaf is not")
            }
        };
    }
    current
}

fn inject_level(level: &Level) -> Result<Obj, ConvertError> {
    // Iterative post-order: Level.depth is 24-bit, so a succ tower can
    // legally exceed the 256-frame host-stack ceiling that used to bound
    // every convert walk.
    let mut done: HashMap<Level, Obj> = HashMap::new();
    let mut stack = vec![(level.clone(), false)];
    while let Some((current, exit)) = stack.pop() {
        if done.contains_key(&current) {
            continue;
        }
        if !exit {
            stack.push((current.clone(), true));
            match current.view() {
                fln_core::level::LevelView::Zero
                | fln_core::level::LevelView::Param(_)
                | fln_core::level::LevelView::MVar(_) => {}
                fln_core::level::LevelView::Succ(child) => stack.push((child.clone(), false)),
                fln_core::level::LevelView::Max(a, b) | fln_core::level::LevelView::IMax(a, b) => {
                    stack.push((b.clone(), false));
                    stack.push((a.clone(), false));
                }
            }
            continue;
        }
        let data = current.data().0.to_le_bytes();
        let object = match current.view() {
            fln_core::level::LevelView::Zero => Obj::mk_nat(0),
            fln_core::level::LevelView::Succ(child) => {
                let inner = done.get(child).ok_or_else(|| {
                    malformed("level", "succ child was not encoded before its parent")
                })?;
                Obj::mk_ctor(TAG_LEVEL_SUCC, vec![inner.clone_ref()], &data)
            }
            fln_core::level::LevelView::Max(a, b) => {
                let left = done
                    .get(a)
                    .ok_or_else(|| malformed("level", "max left was not encoded"))?;
                let right = done
                    .get(b)
                    .ok_or_else(|| malformed("level", "max right was not encoded"))?;
                Obj::mk_ctor(
                    TAG_LEVEL_MAX,
                    vec![left.clone_ref(), right.clone_ref()],
                    &data,
                )
            }
            fln_core::level::LevelView::IMax(a, b) => {
                let left = done
                    .get(a)
                    .ok_or_else(|| malformed("level", "imax left was not encoded"))?;
                let right = done
                    .get(b)
                    .ok_or_else(|| malformed("level", "imax right was not encoded"))?;
                Obj::mk_ctor(
                    TAG_LEVEL_IMAX,
                    vec![left.clone_ref(), right.clone_ref()],
                    &data,
                )
            }
            fln_core::level::LevelView::Param(name) => {
                Obj::mk_ctor(TAG_LEVEL_PARAM, vec![inject_name(name)], &data)
            }
            fln_core::level::LevelView::MVar(id) => {
                Obj::mk_ctor(TAG_LEVEL_MVAR, vec![inject_name(&id.0)], &data)
            }
        };
        done.insert(current, object);
    }
    done.get(level)
        .map(Obj::clone_ref)
        .ok_or_else(|| malformed("level", "level was not encoded"))
}

fn inject_nat(value: u64) -> Obj {
    let maximum = (usize::MAX >> 1) as u64;
    if value <= maximum {
        Obj::mk_nat(value as usize)
    } else {
        Obj::mk_mpz(&[value], false)
    }
}

fn inject_literal(literal: &Literal) -> Obj {
    match literal {
        Literal::Nat(nat) => {
            // Tagged small Nats are `n << 1 | 1`, so the ceiling is
            // `usize::MAX >> 1`, not `usize::MAX`. A single limb of 2^63
            // is a well-formed NatLit; `mk_nat` asserts below that
            // ceiling and would panic — which this membrane forbids.
            // Zero is the empty limb vector and must stay a scalar, not
            // an mpz object.
            let payload = match nat.to_u64() {
                Some(scalar) => inject_nat(scalar),
                None => Obj::mk_mpz(nat.limbs_le(), false),
            };
            Obj::mk_ctor(TAG_LIT_NAT, vec![payload], &[])
        }
        Literal::Str(text) => Obj::mk_ctor(TAG_LIT_STR, vec![Obj::mk_string(text)], &[]),
    }
}

fn inject_level_list(levels: &[Level]) -> Result<Obj, ConvertError> {
    let mut out = Obj::mk_nat(0);
    for level in levels.iter().rev() {
        out = Obj::mk_ctor(TAG_LIST_CONS, vec![inject_level(level)?, out], &[]);
    }
    Ok(out)
}

fn inject_kvmap(map: &KVMap) -> Result<Obj, ConvertError> {
    let mut out = Obj::mk_nat(0);
    for (key, value) in map.entries().iter().rev() {
        let pair = Obj::mk_ctor(0, vec![inject_name(key), inject_data_value(value)?], &[]);
        out = Obj::mk_ctor(TAG_LIST_CONS, vec![pair, out], &[]);
    }
    Ok(out)
}

fn inject_data_value(value: &DataValue) -> Result<Obj, ConvertError> {
    match value {
        DataValue::OfString(text) => {
            Ok(Obj::mk_ctor(TAG_DV_STRING, vec![Obj::mk_string(text)], &[]))
        }
        DataValue::OfBool(flag) => Ok(Obj::mk_ctor(TAG_DV_BOOL, Vec::new(), &[u8::from(*flag)])),
        DataValue::OfName(name) => Ok(Obj::mk_ctor(TAG_DV_NAME, vec![inject_name(name)], &[])),
        DataValue::OfNat(n) => Ok(Obj::mk_ctor(TAG_DV_NAT, vec![inject_nat(*n)], &[])),
        DataValue::OfInt(value) => Ok(Obj::mk_ctor(TAG_DV_INT, vec![Obj::mk_int(*value)], &[])),
        DataValue::OfSyntax(SyntaxHandle(handle)) => {
            Ok(Obj::mk_ctor(TAG_DV_SYNTAX, vec![inject_nat(*handle)], &[]))
        }
    }
}
