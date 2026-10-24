//! Integer linear arithmetic for the pinned `simpArith` post step. The normalizer is
//! untrusted: `Init.Data.Int.Linear` certificates prove every proposed rewrite, including
//! coefficient division and inequality tightening. No arithmetic fact bypasses the kernel.
use super::*;
use fln_bignum::int::BigInt;
use std::collections::BTreeMap;

pub(super) fn integer_type() -> Expr {
    constant("Int")
}

fn integer_neg(a: Expr) -> Expr {
    apply(
        Expr::const_(name("Neg.neg"), vec![Level::zero()]),
        [integer_type(), constant("Int.instNegInt"), a],
    )
}

/// `Lean.mkIntLit`, also the representation used by the pin's `ToExpr Int`.
fn integer_literal(n: &BigInt) -> Expr {
    let magnitude = raw_literal(n.magnitude());
    let positive = apply(
        Expr::const_(name("OfNat.ofNat"), vec![Level::zero()]),
        [
            integer_type(),
            magnitude.clone(),
            Expr::app(constant("instOfNat"), magnitude),
        ],
    );
    if n.is_negative() {
        integer_neg(positive)
    } else {
        positive
    }
}

fn integer_binary(class: &str, operation: &str, instance: &str, a: Expr, b: Expr) -> Expr {
    let instance = apply(
        Expr::const_(name(class), vec![Level::zero()]),
        [integer_type(), constant(instance)],
    );
    apply(
        Expr::const_(name(operation), vec![Level::zero(); 3]),
        [
            integer_type(),
            integer_type(),
            integer_type(),
            instance,
            a,
            b,
        ],
    )
}

fn integer_add(a: Expr, b: Expr) -> Expr {
    integer_binary("instHAdd", "HAdd.hAdd", "Int.instAdd", a, b)
}

fn integer_sub(a: Expr, b: Expr) -> Expr {
    integer_binary("instHSub", "HSub.hSub", "Int.instSub", a, b)
}

fn integer_mul(a: Expr, b: Expr) -> Expr {
    integer_binary("instHMul", "HMul.hMul", "Int.instMul", a, b)
}

fn integer_eq(a: Expr, b: Expr) -> Expr {
    equation(integer_type(), a, b)
}

fn integer_le(a: Expr, b: Expr) -> Expr {
    apply(
        Expr::const_(name("LE.le"), vec![Level::zero()]),
        [integer_type(), constant("Int.instLEInt"), a, b],
    )
}

fn integer_dvd(a: Expr, b: Expr) -> Expr {
    apply(
        Expr::const_(name("Dvd.dvd"), vec![Level::zero()]),
        [integer_type(), constant("Int.instDvd"), a, b],
    )
}

/// Only literal factors are linearized (`getIntValue?`), not arbitrary closed arithmetic.
/// As in the Nat lane, a noncanonical instance stays an atom instead of being assumed to
/// implement the standard operation.
fn integer_value(e: &Expr) -> Option<BigInt> {
    fn positive(e: &Expr) -> Option<BigInt> {
        let args = is_application(e, "OfNat.ofNat", 3)?;
        if !is_constant(args[0], "Int") || is_application(args[2], "instOfNat", 1).is_none() {
            return None;
        }
        let mut value = args[1];
        while let ExprNode::MData { expr, .. } = value.node() {
            value = expr;
        }
        let ExprNode::Lit {
            literal: Literal::Nat(n),
        } = value.node()
        else {
            return None;
        };
        Some(BigInt::from_sign_magnitude(false, big(n)))
    }
    if let Some(n) = positive(e) {
        return Some(n);
    }
    let args = is_application(e, "Neg.neg", 3)?;
    if !is_constant(args[1], "Int.instNegInt") {
        return None;
    }
    positive(args[2]).map(|n| n.neg())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum IntegerExpr {
    Num(BigInt),
    Var(usize),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Neg(Box<Self>),
    MulL(BigInt, Box<Self>),
    MulR(Box<Self>, BigInt),
}

impl IntegerExpr {
    fn increment(self) -> Self {
        Self::Add(Box::new(self), Box::new(Self::Num(BigInt::from_i64(1))))
    }

    fn permute(&mut self, permutation: &[usize]) {
        match self {
            Self::Num(_) => {}
            Self::Var(i) => *i = permutation[*i],
            Self::Add(a, b) | Self::Sub(a, b) => {
                a.permute(permutation);
                b.permute(permutation);
            }
            Self::Neg(a) | Self::MulL(_, a) | Self::MulR(a, _) => a.permute(permutation),
        }
    }

    fn to_term(&self) -> Expr {
        match self {
            Self::Num(n) => Expr::app(constant("Int.Linear.Expr.num"), integer_literal(n)),
            Self::Var(i) => Expr::app(
                constant("Int.Linear.Expr.var"),
                raw_literal(&BigNat::from_u64(*i as u64)),
            ),
            Self::Add(a, b) => apply(constant("Int.Linear.Expr.add"), [a.to_term(), b.to_term()]),
            Self::Sub(a, b) => apply(constant("Int.Linear.Expr.sub"), [a.to_term(), b.to_term()]),
            Self::Neg(a) => Expr::app(constant("Int.Linear.Expr.neg"), a.to_term()),
            Self::MulL(k, a) => apply(
                constant("Int.Linear.Expr.mulL"),
                [integer_literal(k), a.to_term()],
            ),
            Self::MulR(a, k) => apply(
                constant("Int.Linear.Expr.mulR"),
                [a.to_term(), integer_literal(k)],
            ),
        }
    }

    fn denote(&self, atoms: &[Expr]) -> Expr {
        match self {
            Self::Num(n) => integer_literal(n),
            Self::Var(i) => atoms[*i].clone(),
            Self::Add(a, b) => integer_add(a.denote(atoms), b.denote(atoms)),
            Self::Sub(a, b) => integer_sub(a.denote(atoms), b.denote(atoms)),
            Self::Neg(a) => integer_neg(a.denote(atoms)),
            Self::MulL(k, a) => integer_mul(integer_literal(k), a.denote(atoms)),
            Self::MulR(a, k) => integer_mul(a.denote(atoms), integer_literal(k)),
        }
    }
}

/// `Int.Linear.Poly`: nonzero monomials in decreasing variable order and a constant tail.
struct IntegerPoly {
    terms: Vec<(usize, BigInt)>,
    constant: BigInt,
}

impl IntegerPoly {
    fn normalize(e: &IntegerExpr) -> Self {
        fn collect(
            e: &IntegerExpr,
            scale: &BigInt,
            terms: &mut BTreeMap<usize, BigInt>,
            tail: &mut BigInt,
        ) {
            match e {
                IntegerExpr::Num(k) => *tail = tail.add(&scale.mul(k)),
                IntegerExpr::Var(i) => {
                    let coefficient = terms.entry(*i).or_insert_with(BigInt::zero);
                    *coefficient = coefficient.add(scale);
                }
                IntegerExpr::Add(a, b) => {
                    collect(a, scale, terms, tail);
                    collect(b, scale, terms, tail);
                }
                IntegerExpr::Sub(a, b) => {
                    collect(a, scale, terms, tail);
                    collect(b, &scale.neg(), terms, tail);
                }
                IntegerExpr::Neg(a) => collect(a, &scale.neg(), terms, tail),
                IntegerExpr::MulL(k, a) | IntegerExpr::MulR(a, k) => {
                    if !k.is_zero() {
                        collect(a, &scale.mul(k), terms, tail);
                    }
                }
            }
        }
        let mut terms = BTreeMap::new();
        let mut tail = BigInt::zero();
        collect(e, &BigInt::from_i64(1), &mut terms, &mut tail);
        Self {
            terms: terms
                .into_iter()
                .rev()
                .filter(|(_, k)| !k.is_zero())
                .collect(),
            constant: tail,
        }
    }

    fn difference(a: &IntegerExpr, b: &IntegerExpr) -> Self {
        Self::normalize(&IntegerExpr::Sub(Box::new(a.clone()), Box::new(b.clone())))
    }

    fn to_term(&self) -> Expr {
        let mut result = Expr::app(
            constant("Int.Linear.Poly.num"),
            integer_literal(&self.constant),
        );
        for (i, k) in self.terms.iter().rev() {
            result = apply(
                constant("Int.Linear.Poly.add"),
                [
                    integer_literal(k),
                    raw_literal(&BigNat::from_u64(*i as u64)),
                    result,
                ],
            );
        }
        result
    }

    /// The pin's left-associated `Poly.toExpr` / `Poly.denote'`, with unit coefficients
    /// and a zero constant omitted. Keeping this shape matters to `guard_target =ₛ`.
    fn to_linear(&self) -> IntegerExpr {
        let mut result = None;
        for (i, k) in &self.terms {
            let variable = IntegerExpr::Var(*i);
            let monomial = if k == &BigInt::from_i64(1) {
                variable
            } else {
                IntegerExpr::MulL(k.clone(), Box::new(variable))
            };
            result = Some(match result {
                None => monomial,
                Some(previous) => IntegerExpr::Add(Box::new(previous), Box::new(monomial)),
            });
        }
        match result {
            None => IntegerExpr::Num(self.constant.clone()),
            Some(result) if self.constant.is_zero() => result,
            Some(result) => IntegerExpr::Add(
                Box::new(result),
                Box::new(IntegerExpr::Num(self.constant.clone())),
            ),
        }
    }

    fn gcd_coefficients(&self) -> BigInt {
        if self.terms.is_empty() {
            return BigInt::from_i64(1);
        }
        let gcd = self
            .terms
            .iter()
            .fold(BigNat::zero(), |gcd, (_, k)| gcd.gcd(k.magnitude()));
        BigInt::from_sign_magnitude(false, gcd)
    }

    /// `Poly.gcdCoeffs`: a constant polynomial preserves the divisor's sign.
    fn gcd_with(&self, divisor: &BigInt) -> BigInt {
        self.terms.iter().fold(divisor.clone(), |gcd, (_, k)| {
            BigInt::from_sign_magnitude(false, gcd.magnitude().gcd(k.magnitude()))
        })
    }

    /// `Poly.div` divides monomials exactly, but rounds the constant UP. Truncation or
    /// floor division here would be unsound for negative offsets in integer inequalities.
    fn divide(&self, divisor: &BigInt) -> Self {
        Self {
            terms: self
                .terms
                .iter()
                .map(|(i, k)| (*i, k.ediv(divisor)))
                .collect(),
            constant: self.constant.neg().ediv(divisor).neg(),
        }
    }
}

fn atom(atoms: &mut Atoms, e: &Expr) -> IntegerExpr {
    if let Some(i) = atoms.atoms.iter().position(|a| a == e) {
        return IntegerExpr::Var(i);
    }
    atoms.atoms.push(e.clone());
    IntegerExpr::Var(atoms.atoms.len() - 1)
}

/// The pin sorts Int atoms in reverse expression order because its polynomials sort
/// variables in decreasing index order. This leaves the visible monomials in Expr.lt order.
fn sorted_atoms(atoms: Vec<Expr>) -> (Vec<Expr>, Vec<usize>) {
    let (mut atoms, mut permutation) = sort_atoms(atoms);
    atoms.reverse();
    for i in &mut permutation {
        *i = atoms.len() - 1 - *i;
    }
    (atoms, permutation)
}

fn integer_context(atoms: &[Expr]) -> Expr {
    fn go(atoms: &[Expr], lower: usize, upper: usize) -> Expr {
        if lower + 1 == upper {
            return apply(
                Expr::const_(name("Lean.RArray.leaf"), vec![Level::zero()]),
                [integer_type(), atoms[lower].clone()],
            );
        }
        let middle = (lower + upper) / 2;
        apply(
            Expr::const_(name("Lean.RArray.branch"), vec![Level::zero()]),
            [
                integer_type(),
                raw_literal(&BigNat::from_u64(middle as u64)),
                go(atoms, lower, middle),
                go(atoms, middle, upper),
            ],
        )
    }
    if atoms.is_empty() {
        apply(
            Expr::const_(name("Lean.RArray.leaf"), vec![Level::zero()]),
            [integer_type(), integer_literal(&BigInt::zero())],
        )
    } else {
        go(atoms, 0, atoms.len())
    }
}

impl Context {
    fn simp_arith_integer_linear(
        &mut self,
        atoms: &mut Atoms,
        e: &Expr,
        depth: usize,
    ) -> Result<IntegerExpr, NatDefinitionElabError> {
        self.simp_arith_budget(atoms, depth)?;
        if let ExprNode::MData { expr, .. } = e.node() {
            return self.simp_arith_integer_linear(atoms, expr, depth + 1);
        }
        let Some((head, args)) = const_application(e) else {
            return Ok(atom(atoms, e));
        };
        let head = head.to_display_string();
        let binary = match (head.as_str(), args.len()) {
            ("OfNat.ofNat", 3) => {
                return Ok(integer_value(e)
                    .map(IntegerExpr::Num)
                    .unwrap_or_else(|| atom(atoms, e)));
            }
            ("Int.neg", 1) => {
                return Ok(IntegerExpr::Neg(Box::new(self.simp_arith_integer_linear(
                    atoms,
                    args[0],
                    depth + 1,
                )?)));
            }
            ("Neg.neg", 3) if is_constant(args[1], "Int.instNegInt") => {
                return Ok(IntegerExpr::Neg(Box::new(self.simp_arith_integer_linear(
                    atoms,
                    args[2],
                    depth + 1,
                )?)));
            }
            ("Int.add", 2) => Some(("add", 0, 1)),
            ("Int.sub", 2) => Some(("sub", 0, 1)),
            ("Int.mul", 2) => Some(("mul", 0, 1)),
            ("Add.add", 4) if is_constant(args[1], "Int.instAdd") => Some(("add", 2, 3)),
            ("Sub.sub", 4) if is_constant(args[1], "Int.instSub") => Some(("sub", 2, 3)),
            ("Mul.mul", 4) if is_constant(args[1], "Int.instMul") => Some(("mul", 2, 3)),
            ("HAdd.hAdd", 6) if is_heterogeneous_instance(args[3], "instHAdd", "Int.instAdd") => {
                Some(("add", 4, 5))
            }
            ("HSub.hSub", 6) if is_heterogeneous_instance(args[3], "instHSub", "Int.instSub") => {
                Some(("sub", 4, 5))
            }
            ("HMul.hMul", 6) if is_heterogeneous_instance(args[3], "instHMul", "Int.instMul") => {
                Some(("mul", 4, 5))
            }
            _ => None,
        };
        let Some((operation, a, b)) = binary else {
            return Ok(atom(atoms, e));
        };
        let (a, b) = (args[a], args[b]);
        if operation == "mul" {
            if let Some(k) = integer_value(a) {
                return Ok(IntegerExpr::MulL(
                    k,
                    Box::new(self.simp_arith_integer_linear(atoms, b, depth + 1)?),
                ));
            }
            if let Some(k) = integer_value(b) {
                return Ok(IntegerExpr::MulR(
                    Box::new(self.simp_arith_integer_linear(atoms, a, depth + 1)?),
                    k,
                ));
            }
            return Ok(atom(atoms, e));
        }
        let a = Box::new(self.simp_arith_integer_linear(atoms, a, depth + 1)?);
        let b = Box::new(self.simp_arith_integer_linear(atoms, b, depth + 1)?);
        Ok(if operation == "add" {
            IntegerExpr::Add(a, b)
        } else {
            IntegerExpr::Sub(a, b)
        })
    }

    fn simp_arith_integer_certificate(
        &self,
        lemma: &str,
        mut args: Vec<Expr>,
        original: Expr,
        replacement: Expr,
        prop: bool,
    ) -> Result<ArithStep, NatDefinitionElabError> {
        self.simp_arith_require(&[lemma])?;
        args.push(eager_refl_bool_true());
        let expected = if prop {
            prop_eq(original, replacement.clone())
        } else {
            integer_eq(original, replacement.clone())
        };
        Ok(ArithStep {
            proof: expected_prop(apply(constant(lemma), args), expected),
            replacement,
            prop,
        })
    }

    pub(super) fn simp_arith_int_expression(
        &mut self,
        input: &Expr,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        // The pin does not keep source type ascriptions in the elaborated value. Our
        // checked source terms retain them as identity lets. Read through those lets
        // for recognition; the caller's equality still contains the original input,
        // so its assertions remain obligations of the final kernel-checked transport.
        let input = self.without_source_ascriptions(input)?;
        let mut atoms = Atoms::default();
        let mut e = self.simp_arith_integer_linear(&mut atoms, &input, 0)?;
        let (atoms, permutation) = sorted_atoms(atoms.atoms);
        e.permute(&permutation);
        let p = IntegerPoly::normalize(&e);
        let normalized = p.to_linear();
        if normalized == e {
            return Ok(None);
        }
        self.simp_arith_integer_certificate(
            "Int.Linear.Expr.eq_of_norm_eq",
            vec![integer_context(&atoms), e.to_term(), p.to_term()],
            e.denote(&atoms),
            normalized.denote(&atoms),
            false,
        )
        .map(Some)
    }

    pub(super) fn simp_arith_int_constraint(
        &mut self,
        input: &Expr,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        let input = self.without_source_ascriptions(input)?;
        let input = &input;
        if let Some(args) = is_application(input, "Not", 1) {
            return self.simp_arith_int_negated(args[0], input);
        }
        let equality = is_application(input, "Eq", 3);
        let (a, b, strict, equality, check_modified) = if let Some(args) = equality {
            if !is_constant(args[0], "Int") {
                return Ok(None);
            }
            (args[1], args[2], false, true, true)
        } else {
            let Some((head, args)) = const_application(input) else {
                return Ok(None);
            };
            let (a, b, strict) = match (head.to_display_string().as_str(), args.len()) {
                ("Int.le", 2) => (args[0], args[1], false),
                ("Int.lt", 2) => (args[0], args[1], true),
                ("LE.le", 4) if is_constant(args[1], "Int.instLEInt") => (args[2], args[3], false),
                ("LT.lt", 4) if is_constant(args[1], "Int.instLTInt") => (args[2], args[3], true),
                ("GE.ge", 4) if is_constant(args[1], "Int.instLEInt") => (args[3], args[2], false),
                ("GT.gt", 4) if is_constant(args[1], "Int.instLTInt") => (args[3], args[2], true),
                _ => return Ok(None),
            };
            (a, b, strict, false, head == &name("LE.le"))
        };
        let mut atoms = Atoms::default();
        let mut a = self.simp_arith_integer_linear(&mut atoms, a, 0)?;
        let mut b = self.simp_arith_integer_linear(&mut atoms, b, 0)?;
        if equality
            && matches!(
                (&a, &b),
                (
                    IntegerExpr::Var(_),
                    IntegerExpr::Var(_) | IntegerExpr::Num(_)
                ) | (IntegerExpr::Num(_), IntegerExpr::Var(_))
            )
        {
            return Ok(None);
        }
        if strict {
            a = a.increment();
        }
        let (atoms, permutation) = sorted_atoms(atoms.atoms);
        a.permute(&permutation);
        b.permute(&permutation);
        self.simp_arith_int_relation(a, b, &atoms, equality, check_modified)
    }

    fn simp_arith_int_relation(
        &self,
        a: IntegerExpr,
        b: IntegerExpr,
        atoms: &[Expr],
        equality: bool,
        check_modified: bool,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        let p = IntegerPoly::difference(&a, &b);
        let original = if equality {
            integer_eq(a.denote(atoms), b.denote(atoms))
        } else {
            integer_le(a.denote(atoms), b.denote(atoms))
        };
        let mut args = vec![integer_context(atoms), a.to_term(), b.to_term()];
        if p.terms.is_empty() {
            let valid = if equality {
                p.constant.is_zero()
            } else {
                p.constant.is_zero() || p.constant.is_negative()
            };
            let lemma = match (equality, valid) {
                (true, true) => "Int.Linear.eq_eq_true",
                (true, false) => "Int.Linear.eq_eq_false",
                (false, true) => "Int.Linear.le_eq_true",
                (false, false) => "Int.Linear.le_eq_false",
            };
            return self
                .simp_arith_integer_certificate(
                    lemma,
                    args,
                    original,
                    constant(if valid { "True" } else { "False" }),
                    true,
                )
                .map(Some);
        }
        if check_modified && p.to_linear() == a && b == IntegerExpr::Num(BigInt::zero()) {
            return Ok(None);
        }
        if equality {
            let one = BigInt::from_i64(1);
            let negative_one = BigInt::from_i64(-1);
            match p.terms.as_slice() {
                [(x, k), (y, l)] if k == &one && l == &negative_one && p.constant.is_zero() => {
                    let replacement = integer_eq(atoms[*x].clone(), atoms[*y].clone());
                    if replacement == original {
                        return Ok(None);
                    }
                    args.extend([
                        raw_literal(&BigNat::from_u64(*x as u64)),
                        raw_literal(&BigNat::from_u64(*y as u64)),
                    ]);
                    return self
                        .simp_arith_integer_certificate(
                            "Int.Linear.norm_eq_var",
                            args,
                            original,
                            replacement,
                            true,
                        )
                        .map(Some);
                }
                [(x, k)] if k == &one => {
                    let value = integer_literal(&p.constant.neg());
                    let replacement = integer_eq(atoms[*x].clone(), value.clone());
                    if replacement == original {
                        return Ok(None);
                    }
                    args.extend([raw_literal(&BigNat::from_u64(*x as u64)), value]);
                    return self
                        .simp_arith_integer_certificate(
                            "Int.Linear.norm_eq_var_const",
                            args,
                            original,
                            replacement,
                            true,
                        )
                        .map(Some);
                }
                _ => {}
            }
        }
        let divisor = p.gcd_coefficients();
        let tight = !p.constant.emod(&divisor).is_zero();
        if equality && tight {
            args.push(integer_literal(&divisor));
            return self
                .simp_arith_integer_certificate(
                    "Int.Linear.eq_eq_false_of_divCoeff",
                    args,
                    original,
                    constant("False"),
                    true,
                )
                .map(Some);
        }
        let divides = divisor != BigInt::from_i64(1);
        let normalized = if divides { p.divide(&divisor) } else { p };
        let replacement = if equality {
            integer_eq(
                normalized.to_linear().denote(atoms),
                integer_literal(&BigInt::zero()),
            )
        } else {
            integer_le(
                normalized.to_linear().denote(atoms),
                integer_literal(&BigInt::zero()),
            )
        };
        args.push(normalized.to_term());
        if divides {
            args.push(integer_literal(&divisor));
        }
        let lemma = match (equality, divides, tight) {
            (true, false, _) => "Int.Linear.norm_eq",
            (true, true, _) => "Int.Linear.norm_eq_coeff",
            (false, false, _) => "Int.Linear.norm_le",
            (false, true, false) => "Int.Linear.norm_le_coeff",
            (false, true, true) => "Int.Linear.norm_le_coeff_tight",
        };
        self.simp_arith_integer_certificate(lemma, args, original, replacement, true)
            .map(Some)
    }

    fn simp_arith_int_negated(
        &mut self,
        argument: &Expr,
        original: &Expr,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        let Some((head, args)) = const_application(argument) else {
            return Ok(None);
        };
        if args.len() != 4 || !is_constant(args[0], "Int") {
            return Ok(None);
        }
        let (left, right) = (args[2].clone(), args[3].clone());
        let one = || integer_literal(&BigInt::from_i64(1));
        let (lemma, replacement) = match head.to_display_string().as_str() {
            "LE.le" if is_constant(args[1], "Int.instLEInt") => {
                ("Int.not_le_eq", integer_le(integer_add(right, one()), left))
            }
            "GE.ge" if is_constant(args[1], "Int.instLEInt") => {
                ("Int.not_ge_eq", integer_le(integer_add(left, one()), right))
            }
            "LT.lt" if is_constant(args[1], "Int.instLTInt") => {
                ("Int.not_lt_eq", integer_le(right, left))
            }
            "GT.gt" if is_constant(args[1], "Int.instLTInt") => {
                ("Int.not_gt_eq", integer_le(left, right))
            }
            _ => return Ok(None),
        };
        self.simp_arith_require(&[lemma])?;
        let first = apply(constant(lemma), [args[2].clone(), args[3].clone()]);
        // `simpRel?` disables the already-normal check after pushing a negation through.
        let relation =
            is_application(&replacement, "LE.le", 4).expect("constructed LE application");
        let mut atoms = Atoms::default();
        let mut a = self.simp_arith_integer_linear(&mut atoms, relation[2], 0)?;
        let mut b = self.simp_arith_integer_linear(&mut atoms, relation[3], 0)?;
        let (atoms, permutation) = sorted_atoms(atoms.atoms);
        a.permute(&permutation);
        b.permute(&permutation);
        let Some(next) = self.simp_arith_int_relation(a, b, &atoms, false, false)? else {
            return Ok(Some(ArithStep {
                replacement,
                proof: first,
                prop: true,
            }));
        };
        let proof = apply(
            Expr::const_(name("Eq.trans"), vec![Level::one()]),
            [
                Expr::sort(Level::zero()),
                original.clone(),
                replacement,
                next.replacement.clone(),
                first,
                next.proof,
            ],
        );
        Ok(Some(ArithStep {
            replacement: next.replacement,
            proof,
            prop: true,
        }))
    }

    pub(super) fn simp_arith_int_divisibility(
        &mut self,
        input: &Expr,
    ) -> Result<Option<ArithStep>, NatDefinitionElabError> {
        let input = self.without_source_ascriptions(input)?;
        let Some(args) = is_application(&input, "Dvd.dvd", 4) else {
            return Ok(None);
        };
        if !is_constant(args[0], "Int") || !is_constant(args[1], "Int.instDvd") {
            return Ok(None);
        }
        let Some(divisor) = integer_value(args[2]) else {
            return Ok(None);
        };
        if divisor.is_zero() {
            return Ok(None);
        }
        let mut atoms = Atoms::default();
        let mut e = self.simp_arith_integer_linear(&mut atoms, args[3], 0)?;
        let (atoms, permutation) = sorted_atoms(atoms.atoms);
        e.permute(&permutation);
        let p = IntegerPoly::normalize(&e);
        let gcd = p.gcd_with(&divisor);
        let original = integer_dvd(integer_literal(&divisor), e.denote(&atoms));
        let mut args = vec![
            integer_context(&atoms),
            integer_literal(&divisor),
            e.to_term(),
        ];
        if !p.constant.emod(&gcd).is_zero() {
            return self
                .simp_arith_integer_certificate(
                    "Int.Linear.dvd_eq_false",
                    args,
                    original,
                    constant("False"),
                    true,
                )
                .map(Some);
        }
        let p = p.divide(&gcd);
        let normalized = p.to_linear();
        if e == normalized {
            return Ok(None);
        }
        let divisor = divisor.ediv(&gcd);
        let replacement = integer_dvd(integer_literal(&divisor), normalized.denote(&atoms));
        let lemma = if gcd == BigInt::from_i64(1) {
            args.push(p.to_term());
            "Int.Linear.norm_dvd"
        } else {
            args.extend([
                integer_literal(&divisor),
                p.to_term(),
                integer_literal(&gcd),
            ]);
            "Int.Linear.norm_dvd_gcd"
        };
        self.simp_arith_integer_certificate(lemma, args, original, replacement, true)
            .map(Some)
    }
}
