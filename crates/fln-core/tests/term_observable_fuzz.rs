//! Seeded fuzzing of the term plane's cached observables (bead franken_lean-p8a;
//! AGENTS.md testing policy). The companion to the codec campaign in
//! `fln-hash/tests/canon_fuzz.rs`: that one feeds hostile *bytes* to the decoders,
//! this one feeds hostile *shapes* to the constructors.
//!
//! Every `Expr` and `Level` caches a packed data word — hash, approximate depth,
//! loose-bvar range, and the has-fvar / has-mvar / has-param flags — computed once
//! at construction from its children's words. Nothing rechecks it afterwards: the
//! kernel, the unifier, and every cache key read the cached bits and trust them. A
//! single wrong flag is therefore invisible until it silently changes a defeq
//! result or a cache hit.
//!
//! So the oracle here is **independent recomputation**: walk the term structurally
//! and compare against the cached bits (oracle hierarchy: shadow model, not crash).
//! The walks are iterative, so a deep shape exercises the observables rather than
//! the call stack (bead franken_lean-canon-stack-safe-drop-6gy).
//!
//! D1 closes the dependency universe — no `proptest`, no `arbitrary`. The generator
//! is a seeded LCG, so the campaign replays byte-for-byte from the seed list.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level, LevelView};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};

/// Deterministic generator (LCG). Same seed ⇒ same term, which is what lets the
/// campaign build two independently allocated but structurally identical terms.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn below(&mut self, bound: u64) -> u64 {
        if bound == 0 { 0 } else { self.next() % bound }
    }

    fn name(&mut self, depth: u32) -> Name {
        let mut name = Name::anonymous();
        for _ in 0..depth {
            name = match self.below(3) {
                0 => Name::str(name, format!("c{}", self.below(16))),
                1 => Name::num(name, self.below(4096)),
                _ => return name,
            };
        }
        name
    }

    fn level(&mut self, depth: u32) -> Level {
        if depth == 0 {
            return match self.below(3) {
                0 => Level::zero(),
                1 => Level::param(self.name(2)),
                _ => Level::mvar(LMVarId(self.name(2))),
            };
        }
        match self.below(5) {
            0 => self
                .level(depth - 1)
                .succ()
                .expect("inside the depth covenant"),
            1 => Level::max(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
            2 => Level::imax(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
            _ => self.level(0),
        }
    }

    fn kvmap(&mut self) -> KVMap {
        let mut map = KVMap::new();
        for _ in 0..self.below(3) {
            map.insert(self.name(2), DataValue::OfNat(self.below(64)));
        }
        map
    }

    fn expr(&mut self, depth: u32) -> Expr {
        if depth == 0 {
            return match self.below(7) {
                0 => Expr::bvar(self.below(1 << 19) as u32).expect("inside the range covenant"),
                1 => Expr::fvar(FVarId(self.name(2))),
                2 => Expr::mvar(MVarId(self.name(2))),
                3 => Expr::sort(self.level(2)),
                4 => Expr::lit(Literal::Nat(NatLit::from_u64(self.next()))),
                5 => Expr::lit(Literal::Str(format!("l{}", self.below(64)))),
                _ => Expr::const_(self.name(2), vec![self.level(2), self.level(1)]),
            };
        }
        match self.below(7) {
            0 => Expr::app(self.expr(depth - 1), self.expr(depth - 1)),
            1 => Expr::lam(
                self.name(1),
                self.expr(depth - 1),
                self.expr(depth - 1),
                BinderInfo::Implicit,
            ),
            2 => Expr::forall_e(
                self.name(1),
                self.expr(depth - 1),
                self.expr(depth - 1),
                BinderInfo::StrictImplicit,
            ),
            3 => Expr::let_e(
                self.name(1),
                self.expr(depth - 1),
                self.expr(depth - 1),
                self.expr(depth - 1),
                self.below(2) == 0,
            ),
            4 => Expr::proj(self.name(2), self.below(64), self.expr(depth - 1)),
            5 => Expr::mdata(self.kvmap(), self.expr(depth - 1)),
            _ => self.expr(0),
        }
    }
}

/// What a structural walk says about a term, computed without reading any cached
/// word. This is the shadow model the packed bits are checked against.
#[derive(Default, Debug, PartialEq, Eq)]
struct Observed {
    fvar: bool,
    expr_mvar: bool,
    level_mvar: bool,
    level_param: bool,
}

/// Structural facts about one `Level`, by iterative walk over its constructors.
fn observe_level(level: &Level, into: &mut Observed) {
    let mut pending = vec![level.clone()];
    while let Some(current) = pending.pop() {
        match current.view() {
            LevelView::Zero => {}
            LevelView::Succ(inner) => pending.push(inner.clone()),
            LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                pending.push(a.clone());
                pending.push(b.clone());
            }
            LevelView::Param(_) => into.level_param = true,
            LevelView::MVar(_) => into.level_mvar = true,
        }
    }
}

/// Structural facts about one `Expr`, by iterative walk. Embedded levels are walked
/// too, so the level flags are recomputed end to end rather than read back out of a
/// child's cached word (which would make the check tautological).
fn observe_expr(expr: &Expr) -> Observed {
    let mut out = Observed::default();
    let mut pending = vec![expr.clone()];
    while let Some(current) = pending.pop() {
        match current.node() {
            ExprNode::BVar { .. } | ExprNode::Lit { .. } => {}
            ExprNode::FVar { .. } => out.fvar = true,
            ExprNode::MVar { .. } => out.expr_mvar = true,
            ExprNode::Sort { level } => observe_level(level, &mut out),
            ExprNode::Const { levels, .. } => {
                for level in levels {
                    observe_level(level, &mut out);
                }
            }
            ExprNode::App { f, a } => {
                pending.push(f.clone());
                pending.push(a.clone());
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(binder_type.clone());
                pending.push(body.clone());
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push(type_.clone());
                pending.push(value.clone());
                pending.push(body.clone());
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                pending.push(expr.clone())
            }
        }
    }
    out
}

const SEEDS: [u64; 8] = [
    0x0000_0000_0000_0001,
    0x243f_6a88_85a3_08d3,
    0x1319_8a2e_0370_7344,
    0xa409_3822_299f_31d0,
    0x082e_fa98_ec4e_6c89,
    0x4528_21e6_38d0_1377,
    0xbe54_66cf_34e9_0c6c,
    0xffff_ffff_ffff_ffff,
];

#[test]
fn cached_observables_agree_with_an_independent_structural_walk() {
    let iterations: usize = std::env::var("FLN_TERM_FUZZ_ITERS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(64);

    let mut findings: Vec<String> = Vec::new();
    let mut executed = 0usize;
    let mut with_fvar = 0usize;
    let mut with_mvar = 0usize;
    let mut with_param = 0usize;

    for seed in SEEDS {
        let mut rng = Rng(seed);
        // A second generator on the same seed yields structurally identical but
        // independently allocated terms — the only way to test equality and hash
        // coherence without pointer sharing making it trivial.
        let mut twin_rng = Rng(seed);

        for iteration in 0..iterations {
            let depth = (iteration % 5) as u32 + 1;
            let expr = rng.expr(depth);
            let twin = twin_rng.expr(depth);
            executed += 1;

            let observed = observe_expr(&expr);
            let cached = Observed {
                fvar: expr.has_fvar(),
                expr_mvar: expr.has_expr_mvar(),
                level_mvar: expr.has_level_mvar(),
                level_param: expr.has_level_param(),
            };
            if observed != cached {
                findings.push(format!(
                    "seed={seed:x} iter={iteration}: cached flags {cached:?} disagree with the \
                     structural walk {observed:?}"
                ));
            }
            with_fvar += usize::from(observed.fvar);
            with_mvar += usize::from(observed.expr_mvar || observed.level_mvar);
            with_param += usize::from(observed.level_param);

            // The two accessors are two views of one packed field; they cannot
            // disagree without one of them lying to the kernel.
            if expr.has_loose_bvars() != (expr.loose_bvar_range() > 0) {
                findings.push(format!(
                    "seed={seed:x} iter={iteration}: has_loose_bvars={} but loose_bvar_range={}",
                    expr.has_loose_bvars(),
                    expr.loose_bvar_range()
                ));
            }

            // Structural twins must be equal, and equal terms must hash equal —
            // the property every cache key in the program rests on.
            if expr != twin {
                findings.push(format!(
                    "seed={seed:x} iter={iteration}: independently built structural twins compare \
                     unequal"
                ));
            }
            if expr.hash() != twin.hash() {
                findings.push(format!(
                    "seed={seed:x} iter={iteration}: structural twins hash differently ({} vs {})",
                    expr.hash(),
                    twin.hash()
                ));
            }
            if expr == twin && expr.data() != twin.data() {
                findings.push(format!(
                    "seed={seed:x} iter={iteration}: equal terms carry different data words"
                ));
            }

            // A composite is never shallower than its children unless the field has
            // saturated, and saturation is sticky.
            let child_depth = match expr.node() {
                ExprNode::App { f, a } => Some(f.approx_depth().max(a.approx_depth())),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => Some(binder_type.approx_depth().max(body.approx_depth())),
                _ => None,
            };
            if let Some(child) = child_depth
                && expr.approx_depth() < child
                && expr.approx_depth() != u8::MAX
            {
                findings.push(format!(
                    "seed={seed:x} iter={iteration}: approx_depth {} is below a child's {child}",
                    expr.approx_depth()
                ));
            }

            // Formatting is a total operation on every shape (bead
            // franken_lean-canon-stack-safe-drop-6gy); a panic here fails the test.
            let rendered = format!("{expr:?}");
            if rendered.is_empty() {
                findings.push(format!(
                    "seed={seed:x} iter={iteration}: Debug rendered nothing"
                ));
            }
        }
    }

    assert!(
        findings.is_empty(),
        "term-observable findings ({} across {executed} terms):\n{}",
        findings.len(),
        findings.join("\n")
    );

    // Campaign validators: a generator that never emits an fvar, an mvar, or a
    // universe parameter would satisfy every assertion above while testing none of
    // the flags that matter.
    assert!(executed > 200, "campaign executed only {executed} terms");
    assert!(
        with_fvar > 10,
        "only {with_fvar} terms contained a free variable"
    );
    assert!(
        with_mvar > 10,
        "only {with_mvar} terms contained a metavariable"
    );
    assert!(
        with_param > 10,
        "only {with_param} terms contained a universe parameter"
    );
}
