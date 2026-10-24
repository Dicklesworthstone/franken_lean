//! `simp +arith` over `Nat` and `Int`: the pinned simp's `simpArith` post step (vendored
//! `Lean/Meta/Tactic/Simp/Rewrite.lean:303-329`) for linear constraints and terms, and integer
//! divisibility (`Lean/Meta/Tactic/Simp/Arith/{Nat,Int}/{Basic,Simp}.lean`). Every rewrite is a
//! reflection proof over `Init/Data/{Nat,Int}/Linear.lean` (the normalization lemmas and their
//! siblings, closed by `eagerReduce (Eq.refl true)`), which only the kernel decides: the
//! normalizer here is untrusted and a wrong normal form is a kernel rejection, never a proof.
//!
//! Atoms are identified structurally, where the pin's `KExprMap` also accepts a
//! definitionally equal atom, and an operator is recognized only by its canonical instance
//! term (the pin's `Structural` testers), not by the pin's `isDefEqI` fallback.
mod int;

use super::*;
use fln_bignum::nat::BigNat;
use fln_core::expr::NatLit;
use std::cmp::Ordering;

/// `Nat.Linear.fixedVar` (`Init/Data/Nat/Linear.lean:33`): the variable numerals multiply.
const FIXED_VAR: usize = 100_000_000;
/// `exponentiation.threshold`'s default, read by `evalNat`'s `checkExponent`.
const EXPONENT_THRESHOLD: u32 = 256;
/// The deepest term the recursive walks below follow, and the most nodes one linear expression
/// may have. Beyond either is a typed resource refusal, never a different normal form.
const MAX_LINEAR_DEPTH: usize = 256;
const MAX_LINEAR_NODES: usize = 1024;

fn name(path: &str) -> Name {
    Name::from_components(path.split('.'))
}

fn constant(path: &str) -> Expr {
    Expr::const_(name(path), Vec::new())
}

fn nat_type() -> Expr {
    constant("Nat")
}

fn big(n: &NatLit) -> BigNat {
    BigNat::from_limbs_le(n.limbs_le().to_vec())
}

fn raw_literal(n: &BigNat) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_limbs_le(n.limbs_le().to_vec())))
}

fn apply(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

/// `mkNatLit`: `@OfNat.ofNat Nat n (instOfNatNat n)`.
fn nat_literal(n: &BigNat) -> Expr {
    apply(
        Expr::const_(name("OfNat.ofNat"), vec![Level::zero()]),
        [
            nat_type(),
            raw_literal(n),
            Expr::app(constant("instOfNatNat"), raw_literal(n)),
        ],
    )
}

fn nat_binary(class: &str, operation: &str, instance: &str, a: Expr, b: Expr) -> Expr {
    let levels = vec![Level::zero(), Level::zero(), Level::zero()];
    let instance = apply(
        Expr::const_(name(class), vec![Level::zero()]),
        [nat_type(), constant(instance)],
    );
    apply(
        Expr::const_(name(operation), levels),
        [nat_type(), nat_type(), nat_type(), instance, a, b],
    )
}

/// `mkNatAdd`.
fn nat_add(a: Expr, b: Expr) -> Expr {
    nat_binary("instHAdd", "HAdd.hAdd", "instAddNat", a, b)
}

/// `mkNatMul`.
fn nat_mul(a: Expr, b: Expr) -> Expr {
    nat_binary("instHMul", "HMul.hMul", "instMulNat", a, b)
}

/// `mkNatLE`.
fn nat_le(a: Expr, b: Expr) -> Expr {
    apply(
        Expr::const_(name("LE.le"), vec![Level::zero()]),
        [nat_type(), constant("instLENat"), a, b],
    )
}

fn equation(type_: Expr, a: Expr, b: Expr) -> Expr {
    apply(Expr::const_(name("Eq"), vec![Level::one()]), [type_, a, b])
}

/// `mkNatEq`.
fn nat_eq(a: Expr, b: Expr) -> Expr {
    equation(nat_type(), a, b)
}

/// `mkPropEq`.
fn prop_eq(a: Expr, b: Expr) -> Expr {
    equation(Expr::sort(Level::zero()), a, b)
}

/// `mkExpectedPropHint`: `@id.{0} expected proof`.
fn expected_prop(proof: Expr, expected: Expr) -> Expr {
    apply(
        Expr::const_(name("id"), vec![Level::zero()]),
        [expected, proof],
    )
}

/// `eagerReflBoolTrue` (`Lean/Expr.lean:2416`).
fn eager_refl_bool_true() -> Expr {
    let truth = constant("Bool.true");
    let bool_ = constant("Bool");
    apply(
        Expr::const_(name("eagerReduce"), vec![Level::zero()]),
        [
            equation(bool_.clone(), truth.clone(), truth.clone()),
            apply(
                Expr::const_(name("Eq.refl"), vec![Level::one()]),
                [bool_, truth],
            ),
        ],
    )
}

/// `Nat.Linear.Expr` (`Init/Data/Nat/Linear.lean:39-45`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Linear {
    Num(BigNat),
    Var(usize),
    Add(Box<Linear>, Box<Linear>),
    MulL(BigNat, Box<Linear>),
    MulR(Box<Linear>, BigNat),
}

/// `Nat.Linear.Poly`: coefficient and variable, `FIXED_VAR` for numerals.
type Poly = Vec<(BigNat, usize)>;

/// `Nat.Linear.ExprCnstr` and, with `Poly` sides, `PolyCnstr`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Constraint<T> {
    eq: bool,
    lhs: T,
    rhs: T,
}

impl Linear {
    /// `Expr.inc`.
    fn inc(self) -> Linear {
        Linear::Add(Box::new(self), Box::new(Linear::Num(BigNat::from_u64(1))))
    }

    /// `Expr.applyPerm`: `permutation[i]` is the sorted position of atom `i`.
    fn apply_permutation(&self, permutation: &[usize]) -> Linear {
        match self {
            Linear::Num(v) => Linear::Num(v.clone()),
            Linear::Var(i) => Linear::Var(permutation.get(*i).copied().unwrap_or(*i)),
            Linear::Add(a, b) => Linear::Add(
                Box::new(a.apply_permutation(permutation)),
                Box::new(b.apply_permutation(permutation)),
            ),
            Linear::MulL(k, a) => {
                Linear::MulL(k.clone(), Box::new(a.apply_permutation(permutation)))
            }
            Linear::MulR(a, k) => {
                Linear::MulR(Box::new(a.apply_permutation(permutation)), k.clone())
            }
        }
    }

    /// `Expr.toPoly`: the difference list of `go`, emitted in order.
    fn to_poly(&self) -> Poly {
        fn go(coefficient: &BigNat, e: &Linear, out: &mut Poly) {
            match e {
                Linear::Num(k) => {
                    if !k.is_zero() {
                        out.push((coefficient.mul(k), FIXED_VAR));
                    }
                }
                Linear::Var(i) => out.push((coefficient.clone(), *i)),
                Linear::Add(a, b) => {
                    go(coefficient, a, out);
                    go(coefficient, b, out);
                }
                Linear::MulL(k, a) | Linear::MulR(a, k) => {
                    if !k.is_zero() {
                        go(&coefficient.mul(k), a, out);
                    }
                }
            }
        }
        let mut out = Vec::new();
        go(&BigNat::from_u64(1), self, &mut out);
        out
    }

    /// `LinearExpr.toArith`.
    fn to_arith(&self, atoms: &[Expr]) -> Expr {
        match self {
            Linear::Num(v) => nat_literal(v),
            Linear::Var(i) => atoms[*i].clone(),
            Linear::Add(a, b) => nat_add(a.to_arith(atoms), b.to_arith(atoms)),
            Linear::MulL(k, a) => nat_mul(nat_literal(k), a.to_arith(atoms)),
            Linear::MulR(a, k) => nat_mul(a.to_arith(atoms), nat_literal(k)),
        }
    }

    /// `LinearExpr.toExpr`: the reflected `Nat.Linear.Expr` term.
    fn to_term(&self) -> Expr {
        let index = |i: usize| nat_literal(&BigNat::from_u64(i as u64));
        match self {
            Linear::Num(v) => Expr::app(constant("Nat.Linear.Expr.num"), nat_literal(v)),
            Linear::Var(i) => Expr::app(constant("Nat.Linear.Expr.var"), index(*i)),
            Linear::Add(a, b) => apply(constant("Nat.Linear.Expr.add"), [a.to_term(), b.to_term()]),
            Linear::MulL(k, a) => apply(
                constant("Nat.Linear.Expr.mulL"),
                [nat_literal(k), a.to_term()],
            ),
            Linear::MulR(a, k) => apply(
                constant("Nat.Linear.Expr.mulR"),
                [a.to_term(), nat_literal(k)],
            ),
        }
    }
}

/// `Poly.insert`.
fn poly_insert(k: BigNat, v: usize, p: &mut Poly) {
    for index in 0..p.len() {
        let existing = p[index].1;
        if v < existing {
            p.insert(index, (k, v));
            return;
        }
        if v == existing {
            p[index].0 = k.add(&p[index].0);
            return;
        }
    }
    p.push((k, v));
}

/// `Poly.norm`.
fn poly_norm(p: &Poly) -> Poly {
    let mut result = Vec::new();
    for (k, v) in p {
        poly_insert(k.clone(), *v, &mut result);
    }
    result
}

/// `Poly.cancel` (`cancelAux` with `hugeFuel`, which no expression bounded here exhausts).
fn poly_cancel(m1: &Poly, m2: &Poly) -> (Poly, Poly) {
    let (mut r1, mut r2) = (Vec::new(), Vec::new());
    let (mut i, mut j) = (0, 0);
    loop {
        if j == m2.len() {
            r1.extend(m1[i..].iter().cloned());
            return (r1, r2);
        }
        if i == m1.len() {
            r2.extend(m2[j..].iter().cloned());
            return (r1, r2);
        }
        let ((k1, v1), (k2, v2)) = (&m1[i], &m2[j]);
        if v1 < v2 {
            r1.push((k1.clone(), *v1));
            i += 1;
        } else if v2 < v1 {
            r2.push((k2.clone(), *v2));
            j += 1;
        } else {
            match k1.cmp(k2) {
                Ordering::Less => r2.push((k2.sub(k1), *v1)),
                Ordering::Greater => r1.push((k1.sub(k2), *v1)),
                Ordering::Equal => {}
            }
            i += 1;
            j += 1;
        }
    }
}

/// `Poly.isNonZero`: the first numeral monomial's coefficient decides.
fn poly_is_nonzero(p: &Poly) -> bool {
    p.iter()
        .find(|(_, v)| *v == FIXED_VAR)
        .is_some_and(|(k, _)| !k.is_zero())
}

/// `Poly.toExpr` with `monomialToExpr`.
fn poly_to_linear(p: &Poly) -> Linear {
    let monomial = |(k, v): &(BigNat, usize)| {
        if *v == FIXED_VAR {
            Linear::Num(k.clone())
        } else if k == &BigNat::from_u64(1) {
            Linear::Var(*v)
        } else {
            Linear::MulL(k.clone(), Box::new(Linear::Var(*v)))
        }
    };
    let Some((first, rest)) = p.split_first() else {
        return Linear::Num(BigNat::zero());
    };
    rest.iter().fold(monomial(first), |e, m| {
        Linear::Add(Box::new(e), Box::new(monomial(m)))
    })
}

impl Constraint<Linear> {
    fn apply_permutation(&self, permutation: &[usize]) -> Self {
        Constraint {
            eq: self.eq,
            lhs: self.lhs.apply_permutation(permutation),
            rhs: self.rhs.apply_permutation(permutation),
        }
    }

    /// `ExprCnstr.toPoly` then `PolyCnstr.norm`.
    fn normalized(&self) -> Constraint<Poly> {
        let (lhs, rhs) = poly_cancel(
            &poly_norm(&self.lhs.to_poly()),
            &poly_norm(&self.rhs.to_poly()),
        );
        Constraint {
            eq: self.eq,
            lhs,
            rhs,
        }
    }

    /// `LinearCnstr.toArith`.
    fn to_arith(&self, atoms: &[Expr]) -> Expr {
        let (lhs, rhs) = (self.lhs.to_arith(atoms), self.rhs.to_arith(atoms));
        if self.eq {
            nat_eq(lhs, rhs)
        } else {
            nat_le(lhs, rhs)
        }
    }

    /// `LinearCnstr.toExpr`.
    fn to_term(&self) -> Expr {
        apply(
            constant("Nat.Linear.ExprCnstr.mk"),
            [
                constant(if self.eq { "Bool.true" } else { "Bool.false" }),
                self.lhs.to_term(),
                self.rhs.to_term(),
            ],
        )
    }
}

impl Constraint<Poly> {
    /// `PolyCnstr.isUnsat`.
    fn is_unsat(&self) -> bool {
        if self.eq {
            (self.lhs.is_empty() && poly_is_nonzero(&self.rhs))
                || (poly_is_nonzero(&self.lhs) && self.rhs.is_empty())
        } else {
            poly_is_nonzero(&self.lhs) && self.rhs.is_empty()
        }
    }

    /// `PolyCnstr.isValid`.
    fn is_valid(&self) -> bool {
        self.lhs.is_empty() && (!self.eq || self.rhs.is_empty())
    }
}

/// `toContextExpr`: the atoms as `RArray.ofArray`'s balanced tree (`Lean/Data/RArray.lean`).
fn context_term(atoms: &[Expr]) -> Expr {
    fn go(atoms: &[Expr], lb: usize, ub: usize) -> Expr {
        let leaf = Expr::const_(name("Lean.RArray.leaf"), vec![Level::zero()]);
        if lb + 1 == ub {
            return apply(leaf, [nat_type(), atoms[lb].clone()]);
        }
        let mid = (lb + ub) / 2;
        apply(
            Expr::const_(name("Lean.RArray.branch"), vec![Level::zero()]),
            [
                nat_type(),
                raw_literal(&BigNat::from_u64(mid as u64)),
                go(atoms, lb, mid),
                go(atoms, mid, ub),
            ],
        )
    }
    if atoms.is_empty() {
        return apply(
            Expr::const_(name("Lean.RArray.leaf"), vec![Level::zero()]),
            [nat_type(), nat_literal(&BigNat::zero())],
        );
    }
    go(atoms, 0, atoms.len())
}

/// An application's constant head, its levels and its arguments, looking through
/// metadata on the outside only (`match_expr`'s `cleanupAnnotations`).
fn const_application(mut e: &Expr) -> Option<(&Name, Vec<&Expr>)> {
    while let ExprNode::MData { expr, .. } = e.node() {
        e = expr;
    }
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = e.node() {
        args.push(a);
        e = f;
    }
    let ExprNode::Const { name, .. } = e.node() else {
        return None;
    };
    args.reverse();
    Some((name, args))
}

fn is_application<'e>(e: &'e Expr, head: &str, arity: usize) -> Option<Vec<&'e Expr>> {
    let (found, args) = const_application(e)?;
    (args.len() == arity && found == &name(head)).then_some(args)
}

fn is_constant(e: &Expr, path: &str) -> bool {
    matches!(const_application(e), Some((found, args)) if args.is_empty() && found == &name(path))
}

/// The pin's `Structural` instance testers (`Lean/Meta/NatInstTesters.lean`).
fn is_heterogeneous_instance(e: &Expr, class: &str, homogeneous: &str) -> bool {
    is_application(e, class, 2).is_some_and(|args| is_constant(args[1], homogeneous))
}

fn is_inst_of_nat_nat(e: &Expr) -> bool {
    is_application(e, "instOfNatNat", 1).is_some()
}

fn is_inst_pow_nat(e: &Expr) -> bool {
    is_application(e, "instPowNat", 2).is_some_and(|args| is_constant(args[1], "instNatPowNat"))
}

/// The type argument of a supported arithmetic class: `Some(true)` for `Nat`, `Some(false)`
/// for `Int` (`isSupportedType`), `None` otherwise.
fn supported_type(type_: &Expr) -> Option<bool> {
    if is_constant(type_, "Nat") {
        Some(true)
    } else if is_constant(type_, "Int") {
        Some(false)
    } else {
        None
    }
}

/// `isLinearPosCnstr`, reporting the carrier.
fn linear_positive_constraint(e: &Expr) -> Option<bool> {
    for (head, arity) in [
        ("Eq", 3),
        ("Ne", 3),
        ("LE.le", 4),
        ("LT.lt", 4),
        ("GT.gt", 4),
        ("GE.ge", 4),
    ] {
        if let Some(args) = is_application(e, head, arity) {
            return supported_type(args[0]);
        }
    }
    None
}

/// `isLinearCnstr`, reporting the carrier.
fn linear_constraint(e: &Expr) -> Option<bool> {
    match is_application(e, "Not", 1) {
        Some(args) => linear_positive_constraint(args[0]),
        None => linear_positive_constraint(e),
    }
}

/// `isLinearTerm?`, reporting the carrier.
fn linear_term(e: &Expr) -> Option<bool> {
    if let Some(args) =
        is_application(e, "HAdd.hAdd", 6).or_else(|| is_application(e, "HMul.hMul", 6))
    {
        return supported_type(args[0]);
    }
    if let Some(args) =
        is_application(e, "HSub.hSub", 6).or_else(|| is_application(e, "Neg.neg", 3))
    {
        return is_constant(args[0], "Int").then_some(false);
    }
    is_application(e, "Nat.succ", 1).map(|_| true)
}

/// `isDvdCnstr`, reporting the carrier.
fn divisibility(e: &Expr) -> Option<bool> {
    is_application(e, "Dvd.dvd", 4).and_then(|args| supported_type(args[0]))
}

/// `Expr.lt` (vendored `src/library/expr_lt.cpp`, `use_hash = false`): the order `sortExprs`
/// numbers atoms by, which decides the order of a normal form's monomials.
fn expr_lt(a: &Expr, b: &Expr) -> bool {
    fn kind(e: &Expr) -> u8 {
        match e.node() {
            ExprNode::BVar { .. } => 0,
            ExprNode::FVar { .. } => 1,
            ExprNode::MVar { .. } => 2,
            ExprNode::Sort { .. } => 3,
            ExprNode::Const { .. } => 4,
            ExprNode::App { .. } => 5,
            ExprNode::Lam { .. } => 6,
            ExprNode::ForallE { .. } => 7,
            ExprNode::LetE { .. } => 8,
            ExprNode::Lit { .. } => 9,
            ExprNode::MData { .. } => 10,
            ExprNode::Proj { .. } => 11,
        }
    }
    let mut a = a;
    let mut b = b;
    loop {
        if a.allocation_identity() == b.allocation_identity() {
            return false;
        }
        if kind(a) != kind(b) {
            return kind(a) < kind(b);
        }
        if a == b {
            return false;
        }
        match (a.node(), b.node()) {
            (ExprNode::Lit { literal: x }, ExprNode::Lit { literal: y }) => return x.lt(y),
            (ExprNode::BVar { idx: x }, ExprNode::BVar { idx: y }) => return x < y,
            (ExprNode::MData { expr: x, .. }, ExprNode::MData { expr: y, .. }) => {
                if x == y {
                    return false;
                }
                (a, b) = (x, y);
            }
            (
                ExprNode::Proj {
                    struct_name: n,
                    idx: i,
                    expr: x,
                },
                ExprNode::Proj {
                    struct_name: m,
                    idx: j,
                    expr: y,
                },
            ) => {
                if x != y {
                    (a, b) = (x, y);
                } else if n != m {
                    return name_lt(n, m);
                } else {
                    return i < j;
                }
            }
            (ExprNode::Const { name: n, levels: u }, ExprNode::Const { name: m, levels: v }) => {
                return if n != m {
                    name_lt(n, m)
                } else {
                    levels_lt(u, v)
                };
            }
            (ExprNode::App { f, a: x }, ExprNode::App { f: g, a: y }) => {
                if f != g {
                    (a, b) = (f, g);
                } else {
                    (a, b) = (x, y);
                }
            }
            (
                ExprNode::Lam {
                    binder_type: s,
                    body: x,
                    ..
                },
                ExprNode::Lam {
                    binder_type: t,
                    body: y,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: s,
                    body: x,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: t,
                    body: y,
                    ..
                },
            ) => {
                if s != t {
                    (a, b) = (s, t);
                } else {
                    (a, b) = (x, y);
                }
            }
            (
                ExprNode::LetE {
                    type_: s,
                    value: x,
                    body: p,
                    non_dep: d,
                    ..
                },
                ExprNode::LetE {
                    type_: t,
                    value: y,
                    body: q,
                    non_dep: e,
                    ..
                },
            ) => {
                if d != e {
                    return !d & e;
                } else if s != t {
                    (a, b) = (s, t);
                } else if x != y {
                    (a, b) = (x, y);
                } else {
                    (a, b) = (p, q);
                }
            }
            (ExprNode::Sort { level: u }, ExprNode::Sort { level: v }) => return level_lt(u, v),
            (ExprNode::FVar { id: x }, ExprNode::FVar { id: y }) => return name_lt(&x.0, &y.0),
            (ExprNode::MVar { id: x }, ExprNode::MVar { id: y }) => return name_lt(&x.0, &y.0),
            _ => return false,
        }
    }
}

/// The kernel's `name::cmp_core` (`src/util/name.cpp:191`): components from the root, a
/// numeral before a string, a proper prefix first. Not `Name`'s `Ord`, which is `Name.cmp`.
fn name_lt(a: &Name, b: &Name) -> bool {
    fn components(n: &Name) -> Vec<Name> {
        let mut out = Vec::new();
        let mut current = n.clone();
        while !current.is_anonymous() {
            out.push(current.clone());
            current = current.parent();
        }
        out.reverse();
        out
    }
    let (left, right) = (components(a), components(b));
    for (x, y) in left.iter().zip(&right) {
        match (x.leaf_view(), y.leaf_view()) {
            (LeafView::Num(p), LeafView::Num(q)) if p != q => return p < q,
            (LeafView::Str(p), LeafView::Str(q)) if p != q => return p.as_bytes() < q.as_bytes(),
            (LeafView::Num(_), LeafView::Str(_)) => return true,
            (LeafView::Str(_), LeafView::Num(_)) => return false,
            _ => {}
        }
    }
    left.len() < right.len()
}

/// The kernel's `is_lt` on levels (`src/kernel/level.cpp:174`).
fn level_lt(a: &Level, b: &Level) -> bool {
    fn kind(l: &Level) -> u8 {
        match l.view() {
            LevelView::Zero => 0,
            LevelView::Succ(_) => 1,
            LevelView::Max(..) => 2,
            LevelView::IMax(..) => 3,
            LevelView::Param(_) => 4,
            LevelView::MVar(_) => 5,
        }
    }
    let (mut a, mut b) = (a, b);
    loop {
        if a.depth() != b.depth() {
            return a.depth() < b.depth();
        }
        if kind(a) != kind(b) {
            return kind(a) < kind(b);
        }
        if a == b {
            return false;
        }
        match (a.view(), b.view()) {
            (LevelView::Param(x), LevelView::Param(y)) => return name_lt(x, y),
            (LevelView::MVar(x), LevelView::MVar(y)) => return name_lt(&x.0, &y.0),
            (LevelView::Max(p, q), LevelView::Max(r, s))
            | (LevelView::IMax(p, q), LevelView::IMax(r, s)) => {
                (a, b) = if p != r { (p, r) } else { (q, s) };
            }
            (LevelView::Succ(p), LevelView::Succ(r)) => (a, b) = (p, r),
            _ => return false,
        }
    }
}

fn levels_lt(a: &[Level], b: &[Level]) -> bool {
    for (x, y) in a.iter().zip(b) {
        if x != y {
            return level_lt(x, y);
        }
    }
    a.len() < b.len()
}

/// `sortExprs`: the atoms in `Expr.lt` order, and each original atom's new position.
fn sort_atoms(atoms: Vec<Expr>) -> (Vec<Expr>, Vec<usize>) {
    let mut indexed: Vec<(Expr, usize)> =
        atoms.into_iter().enumerate().map(|(i, e)| (e, i)).collect();
    indexed.sort_by(|(x, _), (y, _)| {
        if expr_lt(x, y) {
            Ordering::Less
        } else if expr_lt(y, x) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    });
    let mut permutation = vec![0; indexed.len()];
    for (position, (_, original)) in indexed.iter().enumerate() {
        permutation[*original] = position;
    }
    (indexed.into_iter().map(|(e, _)| e).collect(), permutation)
}

/// `ToLinear.State`: the atoms in first-occurrence order.
#[derive(Default)]
struct Atoms {
    atoms: Vec<Expr>,
    nodes: usize,
}

impl Atoms {
    /// `addAsVar`.
    fn add(&mut self, e: &Expr) -> Linear {
        if let Some(index) = self.atoms.iter().position(|atom| atom == e) {
            return Linear::Var(index);
        }
        self.atoms.push(e.clone());
        Linear::Var(self.atoms.len() - 1)
    }
}

/// The step `simpArith` takes at one node: its replacement and the proof `node = replacement`.
pub(super) struct ArithStep {
    pub replacement: Expr,
    pub proof: Expr,
    pub prop: bool,
}

impl Context {
    /// `simp`'s configuration slot. Only `+arith`, `(arith := true)` and
    /// `(config := { arith := true })` are read; every other item stays the typed refusal it
    /// was. `arith` is honoured as the pin's `updateArith` does: off while the environment lacks
    /// `Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq`.
    pub(super) fn simp_arith_config(
        &mut self,
        config: &Syntax,
        accepts_arith: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        const EXPECTED: &str = "default simplification configuration";
        let unsupported = || NatDefinitionElabError::UnexpectedSyntax { expected: EXPECTED };
        let items = match config {
            Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Tactic", "optConfig"]) => {
                let [items] = args.as_slice() else {
                    return Err(unsupported());
                };
                expect_null_args(items, EXPECTED)?
            }
            _ => {
                expect_empty_null(config, EXPECTED)?;
                return Ok(false);
            }
        };
        if items.is_empty() {
            return Ok(false);
        }
        if !accepts_arith {
            return Err(unsupported());
        }
        for item in items {
            self.tick()?;
            let [item] = expect_node(item, &parser_kind(&["Tactic", "configItem"]), 1, EXPECTED)?
            else {
                return Err(unsupported());
            };
            let Syntax::Node { kind, args, .. } = item else {
                return Err(unsupported());
            };
            let enables = if kind == &parser_kind(&["Tactic", "posConfigItem"]) {
                matches!(args.as_slice(), [Syntax::Atom { val, .. }, Syntax::Ident { val: field, .. }]
                    if val == "+" && field == &name("arith"))
            } else if kind == &parser_kind(&["Tactic", "valConfigItem"]) {
                match args.as_slice() {
                    [
                        Syntax::Atom { val: open, .. },
                        Syntax::Ident { val: field, .. },
                        Syntax::Atom { val: assign, .. },
                        value,
                        Syntax::Atom { val: close, .. },
                    ] if open == "(" && assign == ":=" && close == ")" => {
                        if field == &name("arith") {
                            is_true_literal(value)
                        } else if field == &name("config") {
                            is_arith_structure(value)
                        } else {
                            false
                        }
                    }
                    _ => false,
                }
            } else {
                false
            };
            if !enables {
                return Err(unsupported());
            }
        }
        Ok(self
            .txn
            .env
            .contains(&name("Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq")))
    }

    /// One `simpArith` rewrite of `target`: the first node, children before parents, that the
    /// pin's post step changes, with the proof `node = replacement`. Only closed nodes are
    /// candidates; a node under a binder that mentions it is reached by the binder walk.
    pub(super) fn simp_arith_evidence(
        &mut self,
        target: &Expr,
    ) -> Result<Option<(Typed, Expr)>, NatDefinitionElabError> {
        // (term, whether its parent is a linear term or constraint, children pushed)
        let mut stack: Vec<(&Expr, bool, bool)> = vec![(target, false, false)];
        let mut seen = HashSet::new();
        while let Some((term, parent_target, expanded)) = stack.pop() {
            self.tick()?;
            if !expanded {
                if !seen.insert((term.allocation_identity(), parent_target)) {
                    continue;
                }
                stack.push((term, parent_target, true));
                let own = if matches!(term.node(), ExprNode::MData { .. }) {
                    parent_target
                } else {
                    linear_term(term).is_some()
                        || linear_constraint(term).is_some()
                        || divisibility(term).is_some()
                };
                for child in self.simp_arith_children(term).into_iter().rev() {
                    stack.push((child, own, false));
                }
                continue;
            }
            if term.has_loose_bvars() {
                continue;
            }
            let Some(step) = self.simp_arith_step(term, parent_target)? else {
                continue;
            };
            // A rewrite to the node itself is no progress, never a step.
            if &step.replacement == term {
                continue;
            }
            let type_ = if step.prop {
                prop_eq(term.clone(), step.replacement)
            } else if linear_term(term) == Some(false) {
                equation(int::integer_type(), term.clone(), step.replacement)
            } else {
                nat_eq(term.clone(), step.replacement)
            };
            return Ok(Some((
                Typed {
                    value: step.proof,
                    type_,
                },
                term.clone(),
            )));
        }
        Ok(None)
    }

    /// The subterms simp visits with `simp` rather than `dsimp`: an application's `eq`
    /// arguments (`getCongrSimpKinds`), never a type, instance or proof argument.
    fn simp_arith_children<'e>(&self, term: &'e Expr) -> Vec<&'e Expr> {
        match term.node() {
            ExprNode::App { .. } => {
                let mut head = term;
                let mut args = Vec::new();
                while let ExprNode::App { f, a } = head.node() {
                    args.push(a);
                    head = f;
                }
                args.reverse();
                let type_ = match head.node() {
                    ExprNode::Const { name, .. } => self
                        .txn
                        .env
                        .find(name)
                        .map(|info| info.constant_val().type_.clone()),
                    ExprNode::FVar { id } => {
                        self.txn.lctx.find(id).map(|local| local.type_.clone())
                    }
                    _ => None,
                };
                let Some(type_) = type_ else {
                    let mut all = vec![head];
                    all.extend(args);
                    return all;
                };
                let visit = self.simp_arith_argument_kinds(&type_, args.len());
                args.into_iter()
                    .zip(visit)
                    .filter_map(|(arg, visit)| visit.then_some(arg))
                    .collect()
            }
            ExprNode::Lam { body, .. } => vec![body],
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                if body.has_loose_bvar(0) {
                    vec![body]
                } else {
                    vec![binder_type, body]
                }
            }
            ExprNode::LetE { value, body, .. } => vec![value, body],
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => vec![expr],
            _ => Vec::new(),
        }
    }

    /// For each of `count` arguments of a function of type `type_`, whether simp rewrites it
    /// (`CongrArgKind.eq`): `getCongrSimpKinds` and `fixKindsForDependencies` over the
    /// declared telescope. An argument past the telescope is rewritten.
    fn simp_arith_argument_kinds(&self, type_: &Expr, count: usize) -> Vec<bool> {
        #[derive(Clone, Copy, PartialEq)]
        enum Kind {
            Eq,
            Fixed,
            Cast,
            SubsingletonInst,
        }
        let mut binders: Vec<(&Expr, BinderInfo)> = Vec::new();
        let mut result = type_;
        while binders.len() < count {
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = result.node()
            else {
                break;
            };
            binders.push((binder_type, *binder_info));
            result = body;
        }
        let n = binders.len();
        // Parameter `i` occurs in the type of parameter `j > i` as `BVar(j - 1 - i)`.
        let depends = |j: usize, i: usize| binders[j].0.has_loose_bvar((j - 1 - i) as u32);
        let mut kinds = Vec::with_capacity(n);
        for i in 0..n {
            let (binder_type, info) = binders[i];
            let kind = if result.has_loose_bvar((n - 1 - i) as u32) {
                Kind::Fixed
            } else if self.simp_arith_is_proof_type(binder_type, &binders[..i]) {
                Kind::Cast
            } else if matches!(info, BinderInfo::InstImplicit) {
                let decidable = matches!(const_application(binder_type), Some((head, _))
                    if head == &name("Decidable"));
                if decidable && (0..i).any(|k| depends(i, k) && kinds[k] == Kind::Eq) {
                    Kind::SubsingletonInst
                } else {
                    Kind::Fixed
                }
            } else {
                Kind::Eq
            };
            kinds.push(kind);
        }
        for i in 0..n {
            if (i + 1..n).any(|j| depends(j, i) && matches!(kinds[j], Kind::Eq | Kind::Fixed)) {
                kinds[i] = Kind::Fixed;
            }
        }
        let mut visit: Vec<bool> = kinds.into_iter().map(|kind| kind == Kind::Eq).collect();
        visit.resize(count, true);
        visit
    }

    /// Whether a binder type is a proposition, so its argument is a proof (`isProp`): a
    /// predicate applied, a parameter whose type ends in `Prop` applied, or a `∀` of either.
    fn simp_arith_is_proof_type(&self, type_: &Expr, outer: &[(&Expr, BinderInfo)]) -> bool {
        fn ends_in_prop(mut type_: &Expr) -> bool {
            while let ExprNode::ForallE { body, .. } = type_.node() {
                type_ = body;
            }
            matches!(type_.node(), ExprNode::Sort { level } if level.is_zero())
        }
        let mut type_ = type_;
        let mut depth = 0usize;
        while let ExprNode::ForallE { body, .. } = type_.node() {
            type_ = body;
            depth += 1;
        }
        let mut head = type_;
        while let ExprNode::App { f, .. } = head.node() {
            head = f;
        }
        match head.node() {
            ExprNode::Const { name, .. } => self
                .txn
                .env
                .find(name)
                .is_some_and(|info| ends_in_prop(&info.constant_val().type_)),
            ExprNode::FVar { id } => self
                .txn
                .lctx
                .find(id)
                .is_some_and(|local| ends_in_prop(&local.type_)),
            ExprNode::BVar { idx } => {
                let idx = *idx as usize;
                idx >= depth
                    && idx - depth < outer.len()
                    && ends_in_prop(outer[outer.len() - 1 - (idx - depth)].0)
            }
            _ => false,
        }
    }

    /// `simpArith` at one node (`Rewrite.lean:303-329`): a linear constraint, a linear term
    /// whose parent is neither a linear term nor a constraint, or a divisibility constraint.
    fn simp_arith_step(
        &mut self,
        term: &Expr,
        parent_target: bool,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        if let Some(natural) = linear_constraint(term) {
            if !natural {
                return self.simp_arith_int_constraint(term);
            }
            return self.simp_arith_constraint(term);
        }
        if let Some(natural) = linear_term(term) {
            if parent_target {
                return Ok(None);
            }
            if !natural {
                return self.simp_arith_int_expression(term);
            }
            return self.simp_arith_expression(term);
        }
        if divisibility(term) == Some(false) {
            return self.simp_arith_int_divisibility(term);
        }
        Ok(None)
    }

    /// `Nat.simpExpr?`.
    fn simp_arith_expression(
        &mut self,
        input: &Expr,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        let mut atoms = Atoms::default();
        let mut e = self.simp_arith_linear(&mut atoms, input, 0)?;
        let mut atoms = atoms.atoms;
        if atoms.len() != 1 {
            let (sorted, permutation) = sort_atoms(atoms);
            e = e.apply_permutation(&permutation);
            atoms = sorted;
        }
        let normalized = poly_to_linear(&poly_norm(&e.to_poly()));
        if normalized == e {
            return Ok(None);
        }
        self.simp_arith_require(&["Nat.Linear.Expr.eq_of_toNormPoly_eq"])?;
        let proof = apply(
            constant("Nat.Linear.Expr.eq_of_toNormPoly_eq"),
            [
                context_term(&atoms),
                e.to_term(),
                normalized.to_term(),
                eager_refl_bool_true(),
            ],
        );
        let replacement = normalized.to_arith(&atoms);
        Ok(Some(ArithStep {
            proof: expected_prop(proof, nat_eq(e.to_arith(&atoms), replacement.clone())),
            replacement,
            prop: false,
        }))
    }

    /// `Nat.simpCnstr?`.
    fn simp_arith_constraint(
        &mut self,
        e: &Expr,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        let Some(args) = is_application(e, "Not", 1) else {
            return self.simp_arith_positive(e);
        };
        let argument = args[0];
        let one = || nat_literal(&BigNat::from_u64(1));
        let (lemma, new, a, b) = if let Some(args) =
            is_application(argument, "LE.le", 4).filter(|args| is_constant(args[0], "Nat"))
        {
            let (a, b) = (args[2], args[3]);
            (
                "Nat.not_le_eq",
                nat_le(nat_add(b.clone(), one()), a.clone()),
                a,
                b,
            )
        } else if let Some(args) =
            is_application(argument, "GE.ge", 4).filter(|args| is_constant(args[0], "Nat"))
        {
            let (a, b) = (args[2], args[3]);
            (
                "Nat.not_ge_eq",
                nat_le(nat_add(a.clone(), one()), b.clone()),
                a,
                b,
            )
        } else if let Some(args) =
            is_application(argument, "LT.lt", 4).filter(|args| is_constant(args[0], "Nat"))
        {
            let (a, b) = (args[2], args[3]);
            ("Nat.not_lt_eq", nat_le(b.clone(), a.clone()), a, b)
        } else if let Some(args) =
            is_application(argument, "GT.gt", 4).filter(|args| is_constant(args[0], "Nat"))
        {
            let (a, b) = (args[2], args[3]);
            ("Nat.not_gt_eq", nat_le(a.clone(), b.clone()), a, b)
        } else {
            return Ok(None);
        };
        self.simp_arith_require(&[lemma])?;
        let first = apply(constant(lemma), [a.clone(), b.clone()]);
        let Some(step) = self.simp_arith_positive(&new)? else {
            return Ok(Some(ArithStep {
                replacement: new,
                proof: first,
                prop: true,
            }));
        };
        self.simp_arith_require(&["Eq.trans"])?;
        let proof = apply(
            Expr::const_(name("Eq.trans"), vec![Level::one()]),
            [
                Expr::sort(Level::zero()),
                e.clone(),
                new,
                step.replacement.clone(),
                first,
                step.proof,
            ],
        );
        Ok(Some(ArithStep {
            replacement: step.replacement,
            proof,
            prop: true,
        }))
    }

    /// `Nat.simpCnstrPos?`.
    fn simp_arith_positive(
        &mut self,
        e: &Expr,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        let mut atoms = Atoms::default();
        let Some(mut c) = self.simp_arith_linear_constraint(&mut atoms, e)? else {
            return Ok(None);
        };
        let mut atoms = atoms.atoms;
        if atoms.len() > 1 {
            let (sorted, permutation) = sort_atoms(atoms);
            c = c.apply_permutation(&permutation);
            atoms = sorted;
        }
        let lhs = c.to_arith(&atoms);
        let normalized = c.normalized();
        let constant_result = if normalized.is_unsat() {
            Some(("False", "Nat.Linear.ExprCnstr.eq_false_of_isUnsat"))
        } else if normalized.is_valid() {
            Some(("True", "Nat.Linear.ExprCnstr.eq_true_of_isValid"))
        } else {
            None
        };
        if let Some((result, lemma)) = constant_result {
            self.simp_arith_require(&[lemma, result])?;
            let replacement = constant(result);
            let proof = apply(
                constant(lemma),
                [context_term(&atoms), c.to_term(), eager_refl_bool_true()],
            );
            return Ok(Some(ArithStep {
                proof: expected_prop(proof, prop_eq(lhs, replacement.clone())),
                replacement,
                prop: true,
            }));
        }
        let normal = Constraint {
            eq: normalized.eq,
            lhs: poly_to_linear(&normalized.lhs),
            rhs: poly_to_linear(&normalized.rhs),
        };
        let replacement = normal.to_arith(&atoms);
        if replacement == lhs {
            return Ok(None);
        }
        self.simp_arith_require(&["Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq"])?;
        let proof = apply(
            constant("Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq"),
            [
                context_term(&atoms),
                c.to_term(),
                normal.to_term(),
                eager_refl_bool_true(),
            ],
        );
        Ok(Some(ArithStep {
            proof: expected_prop(proof, prop_eq(lhs, replacement.clone())),
            replacement,
            prop: true,
        }))
    }

    /// A proof names only declarations the environment has: a prelude without them is a
    /// typed refusal, where the pin would hand its kernel an unknown constant.
    fn simp_arith_require(&self, names: &[&str]) -> Result<(), NatDefinitionElabError> {
        for path in names {
            if !self.txn.env.contains(&name(path)) {
                return Err(failure(SourceInferenceError::UnknownConstant(name(path))));
            }
        }
        Ok(())
    }

    /// `ToLinear.toLinearCnstr?`.
    fn simp_arith_linear_constraint(
        &mut self,
        atoms: &mut Atoms,
        e: &Expr,
    ) -> Result<Option<Constraint<Linear>>, NatDefinitionElabError> {
        let Some((head, args)) = const_application(e) else {
            return Ok(None);
        };
        let head = head.clone();
        let mut side = |this: &mut Self, e: &Expr| this.simp_arith_linear(atoms, e, 0);
        let (eq, lhs, rhs) = if head == name("Eq") && args.len() == 3 {
            if !is_constant(args[0], "Nat") {
                return Ok(None);
            }
            (true, side(self, args[1])?, side(self, args[2])?)
        } else if head == name("Nat.le") && args.len() == 2 {
            (false, side(self, args[0])?, side(self, args[1])?)
        } else if head == name("Nat.lt") && args.len() == 2 {
            (false, side(self, args[0])?.inc(), side(self, args[1])?)
        } else if args.len() == 4 && (head == name("LE.le") || head == name("GE.ge")) {
            if !is_constant(args[1], "instLENat") {
                return Ok(None);
            }
            if head == name("LE.le") {
                (false, side(self, args[2])?, side(self, args[3])?)
            } else {
                let rhs = side(self, args[2])?;
                (false, side(self, args[3])?, rhs)
            }
        } else if args.len() == 4 && (head == name("LT.lt") || head == name("GT.gt")) {
            if !is_constant(args[1], "instLTNat") {
                return Ok(None);
            }
            if head == name("LT.lt") {
                (false, side(self, args[2])?.inc(), side(self, args[3])?)
            } else {
                let rhs = side(self, args[2])?;
                (false, side(self, args[3])?.inc(), rhs)
            }
        } else {
            return Ok(None);
        };
        Ok(Some(Constraint { eq, lhs, rhs }))
    }

    fn simp_arith_budget(
        &mut self,
        atoms: &mut Atoms,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        atoms.nodes += 1;
        if depth > MAX_LINEAR_DEPTH || atoms.nodes > MAX_LINEAR_NODES {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        Ok(())
    }

    /// `ToLinear.toLinearExpr`.
    fn simp_arith_linear(
        &mut self,
        atoms: &mut Atoms,
        e: &Expr,
        depth: usize,
    ) -> Result<Linear, NatDefinitionElabError> {
        self.simp_arith_budget(atoms, depth)?;
        match e.node() {
            ExprNode::Lit {
                literal: Literal::Nat(n),
            } => return Ok(Linear::Num(big(n))),
            ExprNode::MData { expr, .. } => return self.simp_arith_linear(atoms, expr, depth + 1),
            ExprNode::Const { name: found, .. } if found == &name("Nat.zero") => {
                return Ok(Linear::Num(BigNat::zero()));
            }
            ExprNode::App { .. } => {}
            _ => return Ok(atoms.add(e)),
        }
        let Some((head, args)) = const_application(e) else {
            return Ok(atoms.add(e));
        };
        let head = head.clone();
        let recurse = |this: &mut Self, atoms: &mut Atoms, x: &Expr| {
            this.simp_arith_linear(atoms, x, depth + 1)
        };
        let add = |this: &mut Self, atoms: &mut Atoms, a: &Expr, b: &Expr| {
            let a = recurse(this, atoms, a)?;
            let b = recurse(this, atoms, b)?;
            Ok::<_, NatDefinitionElabError>(Linear::Add(Box::new(a), Box::new(b)))
        };
        match (head.to_display_string().as_str(), args.len()) {
            ("OfNat.ofNat", 3) if is_inst_of_nat_nat(args[2]) => recurse(self, atoms, args[1]),
            ("Nat.succ", 1) => Ok(recurse(self, atoms, args[0])?.inc()),
            ("Nat.add", 2) => add(self, atoms, args[0], args[1]),
            ("Add.add", 4) if is_constant(args[1], "instAddNat") => {
                add(self, atoms, args[2], args[3])
            }
            ("HAdd.hAdd", 6) if is_heterogeneous_instance(args[3], "instHAdd", "instAddNat") => {
                add(self, atoms, args[4], args[5])
            }
            ("Nat.mul", 2) => self.simp_arith_multiply(atoms, args[0], args[1], e, depth),
            ("Mul.mul", 4) if is_constant(args[1], "instMulNat") => {
                self.simp_arith_multiply(atoms, args[2], args[3], e, depth)
            }
            ("HMul.hMul", 6) if is_heterogeneous_instance(args[3], "instHMul", "instMulNat") => {
                self.simp_arith_multiply(atoms, args[4], args[5], e, depth)
            }
            _ => Ok(atoms.add(e)),
        }
    }

    /// `toLinearExpr`'s `mul`: a numeral factor on either side, the left one first.
    fn simp_arith_multiply(
        &mut self,
        atoms: &mut Atoms,
        a: &Expr,
        b: &Expr,
        whole: &Expr,
        depth: usize,
    ) -> Result<Linear, NatDefinitionElabError> {
        if let Some(k) = self.simp_arith_evaluate(atoms, a, depth + 1)? {
            let b = self.simp_arith_linear(atoms, b, depth + 1)?;
            return Ok(Linear::MulL(k, Box::new(b)));
        }
        if let Some(k) = self.simp_arith_evaluate(atoms, b, depth + 1)? {
            let a = self.simp_arith_linear(atoms, a, depth + 1)?;
            return Ok(Linear::MulR(Box::new(a), k));
        }
        Ok(atoms.add(whole))
    }

    /// `evalNat` (`Lean/Meta/Offset.lean:26`): a closed `Nat` expression's value, reading
    /// operators by their canonical instances only.
    fn simp_arith_evaluate(
        &mut self,
        atoms: &mut Atoms,
        e: &Expr,
        depth: usize,
    ) -> Result<Option<BigNat>, NatDefinitionElabError> {
        self.simp_arith_budget(atoms, depth)?;
        match e.node() {
            ExprNode::Lit {
                literal: Literal::Nat(n),
            } => return Ok(Some(big(n))),
            ExprNode::MData { expr, .. } => {
                return self.simp_arith_evaluate(atoms, expr, depth + 1);
            }
            ExprNode::Const { name: found, .. } if found == &name("Nat.zero") => {
                return Ok(Some(BigNat::zero()));
            }
            ExprNode::App { .. } => {}
            _ => return Ok(None),
        }
        let Some((head, args)) = const_application(e) else {
            return Ok(None);
        };
        let head = head.to_display_string();
        let mut eval = |this: &mut Self, x: &Expr| this.simp_arith_evaluate(atoms, x, depth + 1);
        // (operation, instance check, operand positions)
        let binary: Option<(&str, bool, usize, usize)> = match (head.as_str(), args.len()) {
            ("OfNat.ofNat", 3) => {
                return if is_inst_of_nat_nat(args[2]) {
                    eval(self, args[1])
                } else {
                    Ok(None)
                };
            }
            ("Nat.succ", 1) => {
                return Ok(eval(self, args[0])?.map(|v| v.add(&BigNat::from_u64(1))));
            }
            ("Nat.add", 2) => Some(("add", true, 0, 1)),
            ("Add.add", 4) => Some(("add", is_constant(args[1], "instAddNat"), 2, 3)),
            ("HAdd.hAdd", 6) => Some((
                "add",
                is_heterogeneous_instance(args[3], "instHAdd", "instAddNat"),
                4,
                5,
            )),
            ("Nat.sub", 2) => Some(("sub", true, 0, 1)),
            ("Sub.sub", 4) => Some(("sub", is_constant(args[1], "instSubNat"), 2, 3)),
            ("HSub.hSub", 6) => Some((
                "sub",
                is_heterogeneous_instance(args[3], "instHSub", "instSubNat"),
                4,
                5,
            )),
            ("Nat.mul", 2) => Some(("mul", true, 0, 1)),
            ("Mul.mul", 4) => Some(("mul", is_constant(args[1], "instMulNat"), 2, 3)),
            ("HMul.hMul", 6) => Some((
                "mul",
                is_heterogeneous_instance(args[3], "instHMul", "instMulNat"),
                4,
                5,
            )),
            ("Nat.div", 2) => Some(("div", true, 0, 1)),
            ("Div.div", 4) => Some(("div", is_constant(args[1], "Nat.instDiv"), 2, 3)),
            ("HDiv.hDiv", 6) => Some((
                "div",
                is_heterogeneous_instance(args[3], "instHDiv", "Nat.instDiv"),
                4,
                5,
            )),
            ("Nat.mod", 2) => Some(("mod", true, 0, 1)),
            ("Mod.mod", 4) => Some(("mod", is_constant(args[1], "Nat.instMod"), 2, 3)),
            ("HMod.hMod", 6) => Some((
                "mod",
                is_heterogeneous_instance(args[3], "instHMod", "Nat.instMod"),
                4,
                5,
            )),
            ("Nat.pow", 2) => Some(("pow", true, 0, 1)),
            ("NatPow.pow", 4) => Some(("pow", is_constant(args[1], "instNatPowNat"), 2, 3)),
            ("Pow.pow", 5) => Some(("pow", is_inst_pow_nat(args[2]), 3, 4)),
            ("HPow.hPow", 6) => Some((
                "pow",
                is_application(args[3], "instHPow", 3).is_some_and(|i| is_inst_pow_nat(i[2])),
                4,
                5,
            )),
            _ => None,
        };
        let Some((operation, instance, left, right)) = binary else {
            return Ok(None);
        };
        if !instance {
            return Ok(None);
        }
        if operation == "pow" {
            // `evalPow`: the exponent first, under `checkExponent`, then the base.
            let Some(exponent) = eval(self, args[right])? else {
                return Ok(None);
            };
            let Some(exponent) = exponent.to_u64().and_then(|n| u32::try_from(n).ok()) else {
                return Ok(None);
            };
            if exponent > EXPONENT_THRESHOLD {
                return Ok(None);
            }
            return Ok(eval(self, args[left])?.map(|base| base.pow(exponent)));
        }
        let Some(a) = eval(self, args[left])? else {
            return Ok(None);
        };
        let Some(b) = eval(self, args[right])? else {
            return Ok(None);
        };
        Ok(Some(match operation {
            "add" => a.add(&b),
            "sub" => {
                if b > a {
                    BigNat::zero()
                } else {
                    a.sub(&b)
                }
            }
            "mul" => a.mul(&b),
            "div" => {
                if b.is_zero() {
                    BigNat::zero()
                } else {
                    a.div(&b)
                }
            }
            _ => {
                if b.is_zero() {
                    a
                } else {
                    a.rem(&b)
                }
            }
        }))
    }
}

fn is_true_literal(value: &Syntax) -> bool {
    matches!(value, Syntax::Ident { val, .. } if val == &name("true") || val == &name("Bool.true"))
}

/// `{ arith := true }`: a structure instance with that one field and nothing else.
fn is_arith_structure(value: &Syntax) -> bool {
    let null = |syntax: &Syntax| -> Option<Vec<Syntax>> {
        match syntax {
            Syntax::Node { kind, args, .. } if kind == &Name::str(Name::anonymous(), "null") => {
                Some(args.clone())
            }
            _ => None,
        }
    };
    let node = |syntax: &Syntax, path: &[&str], arity: usize| -> Option<Vec<Syntax>> {
        match syntax {
            Syntax::Node { kind, args, .. }
                if kind == &parser_kind(path) && args.len() == arity =>
            {
                Some(args.clone())
            }
            _ => None,
        }
    };
    let atom =
        |syntax: &Syntax, text: &str| matches!(syntax, Syntax::Atom { val, .. } if val == text);
    let check = || -> Option<bool> {
        let parts = node(value, &["Term", "structInst"], 6)?;
        if !atom(&parts[0], "{")
            || !null(&parts[1])?.is_empty()
            || !atom(&parts[5], "}")
            || !null(&parts[4])?.is_empty()
        {
            return Some(false);
        }
        let ellipsis = node(&parts[3], &["Term", "optEllipsis"], 1)?;
        if !null(&ellipsis[0])?.is_empty() {
            return Some(false);
        }
        let fields = node(&parts[2], &["Term", "structInstFields"], 1)?;
        let [field] = null(&fields[0])?.try_into().ok()?;
        let field = node(&field, &["Term", "structInstField"], 2)?;
        let lval = node(&field[0], &["Term", "structInstLVal"], 2)?;
        if !matches!(&lval[0], Syntax::Ident { val, .. } if val == &name("arith"))
            || !null(&lval[1])?.is_empty()
        {
            return Some(false);
        }
        let [binders, ascription, definition]: [Syntax; 3] = null(&field[1])?.try_into().ok()?;
        if !null(&binders)?.is_empty() || !null(&ascription)?.is_empty() {
            return Some(false);
        }
        let definition = node(&definition, &["Term", "structInstFieldDef"], 3)?;
        Some(
            atom(&definition[0], ":=")
                && null(&definition[1])?.is_empty()
                && is_true_literal(&definition[2]),
        )
    };
    check() == Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(i: usize) -> Linear {
        Linear::Var(i)
    }
    fn num(v: u64) -> Linear {
        Linear::Num(BigNat::from_u64(v))
    }
    fn add(a: Linear, b: Linear) -> Linear {
        Linear::Add(Box::new(a), Box::new(b))
    }
    fn poly(monomials: &[(u64, usize)]) -> Poly {
        monomials
            .iter()
            .map(|(k, v)| (BigNat::from_u64(*k), *v))
            .collect()
    }

    /// `y + x + x` with `x` numbered first normalizes to `2*x + y`, as the pin's
    /// `simp_nat_arith.lean` goal `(2*x + y = 4) ↔ (y + x + x = 4)` requires.
    #[test]
    fn polynomials_sort_merge_and_print_as_the_pin_does() {
        let e = add(add(var(1), var(0)), var(0));
        let normalized = poly_norm(&e.to_poly());
        assert_eq!(normalized, poly(&[(2, 0), (1, 1)]));
        assert_eq!(
            poly_to_linear(&normalized),
            add(Linear::MulL(BigNat::from_u64(2), Box::new(var(0))), var(1))
        );
        assert_eq!(poly_to_linear(&Vec::new()), num(0));
    }

    /// `a + b + 1 + a < b + 4 + a` is `a ≤ 2` at the pin (`simpCnstr1.lean`, traced).
    #[test]
    fn constraints_cancel_to_the_pins_normal_form() {
        let (a, b) = (var(0), var(1));
        let c = Constraint {
            eq: false,
            lhs: add(
                add(add(add(a.clone(), b.clone()), num(1)), a.clone()),
                num(1),
            ),
            rhs: add(add(b, num(4)), a),
        };
        let n = c.normalized();
        assert_eq!(n.lhs, poly(&[(1, 0)]));
        assert_eq!(n.rhs, poly(&[(2, FIXED_VAR)]));
        assert!(!n.is_unsat() && !n.is_valid());
        // `4 = 8 + a` is unsatisfiable; `a + a ≤ 8 + a + a + b` is valid.
        let unsat = Constraint {
            eq: true,
            lhs: num(4),
            rhs: add(num(8), var(0)),
        };
        assert!(unsat.normalized().is_unsat());
        let valid = Constraint {
            eq: false,
            lhs: add(var(0), var(0)),
            rhs: add(add(add(num(8), var(0)), var(0)), var(1)),
        };
        assert!(valid.normalized().is_valid());
    }

    #[test]
    fn atoms_sort_by_the_kernels_expression_order() {
        let x = Expr::fvar(FVarId(Name::num(Name::from_components(["_uniq"]), 2)));
        let y = Expr::fvar(FVarId(Name::num(Name::from_components(["_uniq"]), 10)));
        let applied = Expr::app(constant("f"), x.clone());
        let (sorted, permutation) = sort_atoms(vec![applied.clone(), y.clone(), x.clone()]);
        assert_eq!(sorted, vec![x, y, applied]);
        assert_eq!(permutation, vec![2, 1, 0]);
        // Components from the root: `a.b` precedes `c`, unlike `Name.cmp`.
        assert!(name_lt(&name("a.b"), &name("c")));
        assert!(name_lt(&Name::num(name("a"), 3), &name("a.b")));
    }
}
