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

use fln_core::expr::{Expr, ExprNode, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_unsafe_abi::handle::Obj;

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

const TAG_EXPR_BVAR: u8 = 0;
const TAG_EXPR_FVAR: u8 = 1;
const TAG_EXPR_SORT: u8 = 3;
const TAG_EXPR_CONST: u8 = 4;
const TAG_EXPR_APP: u8 = 5;
const TAG_EXPR_LIT: u8 = 9;

const TAG_LIT_NAT: u8 = 0;
const TAG_LIT_STR: u8 = 1;

const TAG_LIST_NIL: u8 = 0;
const TAG_LIST_CONS: u8 = 1;

fn malformed(family: &'static str, reason: impl Into<String>) -> ConvertError {
    ConvertError::MalformedCompat {
        family,
        reason: reason.into(),
    }
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

    fn expr(&mut self, obj: &Obj) -> Result<Expr, ConvertError> {
        if obj.is_scalar() {
            return Err(malformed(
                "expr",
                "a bare tagged scalar is not an expression object",
            ));
        }
        let tag = obj.obj_tag() as u8;
        match tag {
            TAG_EXPR_BVAR => {
                let index = obj.ctor_scalar_u64(0) as u32;
                Expr::bvar(index).map_err(|_| ConvertError::NativeOverflow { family: "expr" })
            }
            TAG_EXPR_FVAR => {
                let name = self.name(&obj.ctor_child(0))?;
                Ok(Expr::fvar(fln_core::expr::FVarId(name)))
            }
            TAG_EXPR_SORT => {
                let level = self.level(&obj.ctor_child(0))?;
                Ok(Expr::sort(level))
            }
            TAG_EXPR_CONST => {
                let name = self.name(&obj.ctor_child(0))?;
                let levels = self.level_list(&obj.ctor_child(1))?;
                Ok(Expr::const_(name, levels))
            }
            TAG_EXPR_APP => {
                let f = self.project_expr_child(obj, 0)?;
                let a = self.project_expr_child(obj, 1)?;
                Ok(Expr::app(f, a))
            }
            TAG_EXPR_LIT => {
                let literal = self.literal(&obj.ctor_child(0))?;
                Ok(Expr::lit(literal))
            }
            other => Err(ConvertError::UnsupportedConstructor {
                family: "expr",
                tag: other,
            }),
        }
    }

    fn project_expr_child(&mut self, obj: &Obj, i: usize) -> Result<Expr, ConvertError> {
        let child = obj.ctor_child(i);
        self.expr(&child)
    }

    fn name(&mut self, obj: &Obj) -> Result<Name, ConvertError> {
        if obj.is_scalar() {
            return Err(malformed("name", "a tagged scalar is not a name object"));
        }
        match obj.obj_tag() as u8 {
            TAG_NAME_ANONYMOUS => Ok(Name::anonymous()),
            TAG_NAME_STR => {
                let pre = self.name(&obj.ctor_child(0))?;
                let text = self.string(&obj.ctor_child(1))?;
                Ok(Name::str(pre, text))
            }
            TAG_NAME_NUM => {
                let pre = self.name(&obj.ctor_child(0))?;
                let component = obj.ctor_scalar_u64(0);
                Ok(Name::num(pre, component))
            }
            other => Err(ConvertError::UnsupportedConstructor {
                family: "name",
                tag: other,
            }),
        }
    }

    fn level(&mut self, obj: &Obj) -> Result<Level, ConvertError> {
        if obj.is_scalar() {
            return Err(malformed("level", "a tagged scalar is not a level object"));
        }
        match obj.obj_tag() as u8 {
            TAG_LEVEL_ZERO => Ok(Level::zero()),
            TAG_LEVEL_SUCC => {
                let inner = self.level(&obj.ctor_child(0))?;
                inner
                    .succ()
                    .map_err(|_| ConvertError::NativeOverflow { family: "level" })
            }
            TAG_LEVEL_MAX => {
                let a = self.level(&obj.ctor_child(0))?;
                let b = self.level(&obj.ctor_child(1))?;
                Level::max(a, b).map_err(|_| ConvertError::NativeOverflow { family: "level" })
            }
            TAG_LEVEL_IMAX => {
                let a = self.level(&obj.ctor_child(0))?;
                let b = self.level(&obj.ctor_child(1))?;
                Level::imax(a, b).map_err(|_| ConvertError::NativeOverflow { family: "level" })
            }
            TAG_LEVEL_PARAM => {
                let name = self.name(&obj.ctor_child(0))?;
                Ok(Level::param(name))
            }
            other => Err(ConvertError::UnsupportedConstructor {
                family: "level",
                tag: other,
            }),
        }
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
                let payload = obj.ctor_child(0);
                if payload.is_scalar() {
                    Ok(Literal::Nat(NatLit::from_u64(payload.unbox() as u64)))
                } else {
                    let (sign, size, limbs) = payload.mpz_view();
                    if sign < 0 {
                        return Err(malformed("literal", "a natural literal is negative"));
                    }
                    if size as usize > limbs.len() {
                        return Err(malformed("literal", "mpz size field exceeds the limb span"));
                    }
                    Ok(Literal::Nat(NatLit::from_limbs_le(
                        limbs[..size as usize].to_vec(),
                    )))
                }
            }
            TAG_LIT_STR => {
                let text = self.string(&obj.ctor_child(0))?;
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
            if cursor.is_scalar() {
                return Err(malformed("level-list", "the list ends in a scalar"));
            }
            match cursor.obj_tag() as u8 {
                TAG_LIST_NIL => return Ok(out),
                TAG_LIST_CONS => {
                    out.push(self.level(&cursor.ctor_child(0))?);
                    let tail = cursor.ctor_child(1);
                    cursor = tail;
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

    fn string(&mut self, obj: &Obj) -> Result<String, ConvertError> {
        if obj.is_scalar() {
            return Err(malformed(
                "string",
                "a tagged scalar is not a string object",
            ));
        }
        // `string_view` is `(m_size, m_capacity, m_length, bytes-with-NUL)`.
        // `m_length` is the UTF-8 scalar count, the same field
        // `lean_string_length` boxes. Slicing the buffer with it treats
        // "héllo" (5 scalars, 6 payload bytes) as a 5-byte string and
        // silently drops the last character — or splits a multi-byte
        // scalar and fails UTF-8. The payload is `m_size - 1` bytes.
        let (size, _, length, bytes) = obj.string_view();
        if size == 0 || size > bytes.len() || bytes[size - 1] != 0 {
            return Err(malformed(
                "string",
                "missing NUL terminator or size past the buffer",
            ));
        }
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
    Ok(inject_expr_value(expr))
}

fn inject_expr_value(expr: &Expr) -> Obj {
    match expr.node() {
        ExprNode::BVar { idx } => {
            Obj::mk_ctor(TAG_EXPR_BVAR, Vec::new(), &(*idx as u64).to_le_bytes())
        }
        ExprNode::FVar { id } => Obj::mk_ctor(TAG_EXPR_FVAR, vec![inject_name(&id.0)], &[]),
        ExprNode::Sort { level } => Obj::mk_ctor(TAG_EXPR_SORT, vec![inject_level(level)], &[]),
        ExprNode::Const { name, levels } => Obj::mk_ctor(
            TAG_EXPR_CONST,
            vec![inject_name(name), inject_level_list(levels)],
            &[],
        ),
        ExprNode::App { f, a } => Obj::mk_ctor(
            TAG_EXPR_APP,
            vec![inject_expr_value(f), inject_expr_value(a)],
            &[],
        ),
        ExprNode::Lit { literal } => Obj::mk_ctor(TAG_EXPR_LIT, vec![inject_literal(literal)], &[]),
        other => {
            // Outside the converted subset: the injection boundary is the
            // same as the projection boundary. A well-formed converter
            // pipeline never lands here (projection refuses these tags), so
            // the honest encoding is the subset's own refusal shape.
            unreachable!(
                "inject_expr: constructor outside the converted subset ({other:?}) — \
                 the subset boundary is declared on projection, and this path is unreachable \
                 from any projected term"
            )
        }
    }
}

fn inject_name(name: &Name) -> Obj {
    if name.is_anonymous() {
        return Obj::mk_ctor(TAG_NAME_ANONYMOUS, Vec::new(), &[]);
    }
    let pre = inject_name(&name.parent());
    match name.leaf_view() {
        fln_core::name::LeafView::Str(text) => {
            Obj::mk_ctor(TAG_NAME_STR, vec![pre, Obj::mk_string(text)], &[])
        }
        fln_core::name::LeafView::Num(component) => {
            Obj::mk_ctor(TAG_NAME_NUM, vec![pre], &component.to_le_bytes())
        }
        fln_core::name::LeafView::Anonymous => unreachable!("parent is anonymous but leaf is not"),
    }
}

fn inject_level(level: &Level) -> Obj {
    match level.view() {
        fln_core::level::LevelView::Zero => Obj::mk_ctor(TAG_LEVEL_ZERO, Vec::new(), &[]),
        fln_core::level::LevelView::Succ(inner) => {
            Obj::mk_ctor(TAG_LEVEL_SUCC, vec![inject_level(inner)], &[])
        }
        fln_core::level::LevelView::Max(a, b) => {
            Obj::mk_ctor(TAG_LEVEL_MAX, vec![inject_level(a), inject_level(b)], &[])
        }
        fln_core::level::LevelView::IMax(a, b) => {
            Obj::mk_ctor(TAG_LEVEL_IMAX, vec![inject_level(a), inject_level(b)], &[])
        }
        fln_core::level::LevelView::Param(name) => {
            Obj::mk_ctor(TAG_LEVEL_PARAM, vec![inject_name(name)], &[])
        }
        fln_core::level::LevelView::MVar(_) => unreachable!(
            "inject_level: metavariables are elaboration state, not terms — \
             the subset boundary is declared on projection"
        ),
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
            let maximum = (usize::MAX >> 1) as u64;
            let payload = match nat.to_u64() {
                Some(scalar) if scalar <= maximum => Obj::mk_nat(scalar as usize),
                _ => Obj::mk_mpz(nat.limbs_le(), false),
            };
            Obj::mk_ctor(TAG_LIT_NAT, vec![payload], &[])
        }
        Literal::Str(text) => Obj::mk_ctor(TAG_LIT_STR, vec![Obj::mk_string(text)], &[]),
    }
}

fn inject_level_list(levels: &[Level]) -> Obj {
    let mut out = Obj::mk_ctor(TAG_LIST_NIL, Vec::new(), &[]);
    for level in levels.iter().rev() {
        out = Obj::mk_ctor(TAG_LIST_CONS, vec![inject_level(level), out], &[]);
    }
    out
}
