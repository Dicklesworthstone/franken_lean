//! `h ▸ e`: the pin's `Term.subst` (`Lean/Parser/Term.lean:973`, `trailing_parser:75 " ▸ "
//! >> sepBy1 (termParser 75) " ▸ "`), elaborated by `elabSubst`
//! (`Lean/Elab/BuiltinNotation.lean:457`).
//!
//! `h : a = b` rewrites `e`. With an expected type `T`, the motive abstracts `b` in `T`, or
//! failing that `a` (with `h` reversed by `Eq.symm`); `e` is elaborated against the motive at
//! the other side, and the result is `@Eq.rec α a motive e b h`. Without an expected type,
//! `e`'s own type is abstracted at `a`, or failing that at `b`.
//!
//! Not reproduced, and refused instead of approximated: the pin's retry that also rewrites
//! `e`'s type when it does not check against the motive's instance, and its fallback to
//! `subst` when the motive is not type correct. Abstraction is structural (after
//! instantiation), where the pin's `kabstract` also matches up to instances.
use super::*;

/// Why `▸` was refused: the pin's messages' first lines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubstError {
    /// `h`'s type is not an equality.
    NotEquality,
    /// Neither side of `h` occurs in the expected type.
    ExpectedNotMentioned,
    /// Neither side of `h` occurs in `e`'s type.
    NotMentioned,
}

impl std::fmt::Display for SubstError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotEquality => f.write_str("invalid `▸` notation, argument"),
            Self::ExpectedNotMentioned => {
                f.write_str("invalid `▸` notation, expected result type of cast is ")
            }
            Self::NotMentioned => f.write_str("invalid `▸` notation, the equality"),
        }
    }
}

fn refuse(error: SubstError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Subst(error))
}

/// `Eq.{u} α a b`'s parts.
struct Equality {
    level: Level,
    alpha: Expr,
    lhs: Expr,
    rhs: Expr,
}

fn equality(type_: &Expr) -> Option<Equality> {
    let (head, args) = operators::spine(type_);
    let ExprNode::Const { name, levels } = head.node() else {
        return None;
    };
    if *name != Name::from_components(["Eq"]) || args.len() != 3 || levels.len() != 1 {
        return None;
    }
    Some(Equality {
        level: levels[0].clone(),
        alpha: args[0].clone(),
        lhs: args[1].clone(),
        rhs: args[2].clone(),
    })
}

fn eq(level: &Level, alpha: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["Eq"]), vec![level.clone()]),
                alpha.clone(),
            ),
            lhs,
        ),
        rhs,
    )
}

impl Context {
    /// `Term.subst`'s arguments: `h`, `"▸"`, and the one-element operand list.
    pub(super) fn substitution(
        &mut self,
        args: &[Syntax],
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let [heq_syntax, arrow, operands] = args else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(arrow, "▸", "substitution arrow")?;
        let [operand] = expect_null_args(operands, "substitution operand")? else {
            return Err(failure(SourceInferenceError::Scope));
        };
        // `tryPostponeIfHasMVars?`: an expected type still holding metavariables is not
        // used.
        let expected = match expected {
            Some(expected) => {
                let expected = self.instantiate(expected)?;
                (!expected.has_expr_mvar()).then_some(expected)
            }
            None => None,
        };
        let heq = self.term(heq_syntax, None)?;
        self.flush(false)?;
        let mut proof = self.instantiate(&heq.value)?;
        let heq_type = self.instantiate(&heq.type_)?;
        let parts = match equality(&heq_type) {
            Some(parts) => parts,
            None => {
                let reduced = self.whnf(&heq_type)?;
                equality(&reduced).ok_or_else(|| refuse(SubstError::NotEquality))?
            }
        };
        let Equality {
            level,
            alpha,
            mut lhs,
            mut rhs,
        } = parts;
        let (abstracted, operand) = match expected {
            Some(expected) => {
                let mut abstracted = self.kabstract(&expected, &rhs)?;
                if !abstracted.has_loose_bvars() {
                    abstracted = self.kabstract(&expected, &lhs)?;
                    if !abstracted.has_loose_bvars() {
                        return Err(refuse(SubstError::ExpectedNotMentioned));
                    }
                    proof = self.symm(&level, &alpha, &lhs, &rhs, proof);
                    std::mem::swap(&mut lhs, &mut rhs);
                }
                let operand_expected = self.substitute(&abstracted, &lhs)?;
                let operand = self.term(operand, Some(operand_expected.clone()))?;
                let operand = self.finish_term(operand, Some(&operand_expected))?;
                (abstracted, operand)
            }
            None => {
                let operand = self.term(operand, None)?;
                self.flush(false)?;
                let operand_type = self.instantiate(&operand.type_)?;
                let mut abstracted = self.kabstract(&operand_type, &lhs)?;
                if !abstracted.has_loose_bvars() {
                    abstracted = self.kabstract(&operand_type, &rhs)?;
                    if !abstracted.has_loose_bvars() {
                        return Err(refuse(SubstError::NotMentioned));
                    }
                    proof = self.symm(&level, &alpha, &lhs, &rhs, proof);
                    std::mem::swap(&mut lhs, &mut rhs);
                }
                (abstracted, operand)
            }
        };
        // The motive `fun x (h : lhs = x) => abstracted[x]`, and its universe.
        let result_type = self.substitute(&abstracted, &rhs)?;
        let sort = self
            .known_type(&result_type)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let motive_level = self.sort_level(&Typed {
            value: result_type.clone(),
            type_: sort,
        })?;
        let body = abstracted
            .lift_loose(0, 1)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let x = Expr::bvar(0).map_err(|_| failure(SourceInferenceError::Scope))?;
        let motive = Expr::lam(
            Name::from_components(["x"]),
            alpha.clone(),
            Expr::lam(
                Name::from_components(["h"]),
                eq(&level, &alpha, lhs.clone(), x),
                body,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let rec = Expr::const_(
            Name::from_components(["Eq", "rec"]),
            vec![motive_level, level],
        );
        let value = [alpha, lhs, motive, operand.value, rhs, proof]
            .into_iter()
            .fold(rec, Expr::app);
        Ok(Typed {
            value,
            type_: result_type,
        })
    }

    /// `@Eq.symm α a b h : b = a`.
    fn symm(&self, level: &Level, alpha: &Expr, lhs: &Expr, rhs: &Expr, proof: Expr) -> Expr {
        [alpha.clone(), lhs.clone(), rhs.clone(), proof]
            .into_iter()
            .fold(
                Expr::const_(Name::from_components(["Eq", "symm"]), vec![level.clone()]),
                Expr::app,
            )
    }
}
