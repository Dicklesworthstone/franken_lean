//! `h ▸ e`: the pin's `Term.subst` (`Lean/Parser/Term.lean:973`, `trailing_parser:75 " ▸ "
//! >> sepBy1 (termParser 75) " ▸ "`), elaborated by `elabSubst`
//! (`Lean/Elab/BuiltinNotation.lean:457`).
//!
//! `h : a = b` rewrites `e`. With an expected type `T`, the motive abstracts `b` in `T`, or
//! failing that `a` (with `h` reversed by an ordinary equality recursor); `e` is elaborated against the motive at
//! the other side, and the result is `@Eq.rec α a motive e b h`. Without an expected type,
//! `e`'s own type is abstracted at `a`, or failing that at `b`.
//!
//! A failed operand check retries the pin's reverse transport for a fully inferred local
//! value or explicitly type-ascribed operand. Expected-type-dependent syntax is
//! not reinterpreted without its expected type. The bad-motive `subst` fallback
//! remains unsupported. Abstraction is structural after instantiation.
use super::*;

mod operand;

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
                    proof = self.symm(&level, &alpha, &lhs, &rhs, proof)?;
                    std::mem::swap(&mut lhs, &mut rhs);
                }
                let operand_expected = self.substitute(&abstracted, &lhs)?;
                let oriented = Equality {
                    level: level.clone(),
                    alpha: alpha.clone(),
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };
                let operand =
                    self.substitution_operand(operand, &operand_expected, &oriented, &proof)?;
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
                    proof = self.symm(&level, &alpha, &lhs, &rhs, proof)?;
                    std::mem::swap(&mut lhs, &mut rhs);
                }
                (abstracted, operand)
            }
        };
        self.substitution_transport(
            &Equality {
                level,
                alpha,
                lhs,
                rhs,
            },
            abstracted,
            operand,
            proof,
        )
    }

    /// Build only an ordinary equality recursor. Final declaration admission
    /// checks both this motive and the operand, including an inner retry cast.
    fn substitution_transport(
        &mut self,
        equality: &Equality,
        abstracted: Expr,
        operand: Typed,
        proof: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let Equality {
            level,
            alpha,
            lhs,
            rhs,
        } = equality;
        // The motive `fun x (h : lhs = x) => abstracted[x]`, and its universe.
        let result_type = self.substitute(&abstracted, rhs)?;
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
                eq(level, alpha, lhs.clone(), x),
                body,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let rec = Expr::const_(
            Name::from_components(["Eq", "rec"]),
            vec![motive_level, level.clone()],
        );
        let value = [
            alpha.clone(),
            lhs.clone(),
            motive,
            operand.value,
            rhs.clone(),
            proof,
        ]
        .into_iter()
        .fold(rec, Expr::app);
        Ok(Typed {
            value,
            type_: result_type,
        })
    }

    /// Derive `b = a` from `h : a = b` using only admitted `Eq.rec` and
    /// `Eq.refl`. The minimal source seed deliberately does not declare an
    /// `Eq.symm` helper; neither forward retries nor reverse casts may invent it.
    fn symm(
        &mut self,
        level: &Level,
        alpha: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        proof: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let equality = Equality {
            level: level.clone(),
            alpha: alpha.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        };
        let x = Expr::bvar(0).map_err(|_| failure(SourceInferenceError::Scope))?;
        let abstracted = eq(level, alpha, x, lhs.clone());
        let reflexivity = [alpha.clone(), lhs.clone()].into_iter().fold(
            Expr::const_(Name::from_components(["Eq", "refl"]), vec![level.clone()]),
            Expr::app,
        );
        let operand = Typed {
            value: reflexivity,
            type_: eq(level, alpha, lhs.clone(), lhs.clone()),
        };
        self.substitution_transport(&equality, abstracted, operand, proof)
            .map(|term| term.value)
    }
}
