//! The pin's default `Nat` simplification procedures (vendored
//! `src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Nat.lean`, with `Util.lean` beside it): the
//! `dsimproc`s `Nat.reduceSucc`, `reduceAdd`, `reduceMul`, `reduceSub`, `reduceDiv`, `reduceMod`,
//! `reducePow`, `reduceAnd`, `reduceXor`, `reduceOr`, `reduceShiftLeft`, `reduceShiftRight`,
//! `reduceGcd`, `reduceBEq` and `reduceBNe`, which fold an operation on two numerals into one; the
//! decisions `Nat.reduceLT` and `reduceGT` of two numerals; and the offset procedures
//! `Nat.reduceEqDiff`, `reduceBeqDiff`, `reduceBneDiff`, `reduceLeDiff` and `reduceSubDiff`, which
//! cancel numeral offsets between two sides (`x + 2 = 5` is `x = 3`) through the `Nat.Simproc`
//! lemmas (`src/Init/Data/Nat/Simproc.lean`), with `Nat.reduceDvd`. `Nat.isValue` is `seval`'s
//! only and is not here.
//!
//! The pin runs them after a node's rewrite theorems (`postDefault`, `Rewrite.lean:542-546`:
//! `rewritePost >> userPostSimprocs`), so here they are one rule after every theorem and before
//! `+arith`'s normalization: a procedure rewrites only where no theorem does. Within the rule the
//! first node, children before parents, that a procedure rewrites is taken, and at one node the
//! candidates are tried in the order the pin's discrimination tree returns them (`simp?` at
//! v4.32.0 reports `Nat.reduceSub` on `5 - 3` and `Nat.reduceBEq` on `5 == 3`, not their `Diff`
//! siblings). `simp only` starts with none of them (`mkSimpContext`,
//! `src/Lean/Elab/Tactic/Simp.lean:568`); an argument naming one adds it and `-` erases it.
//!
//! A `dsimproc`'s result has no proof at the pin (`DStep.toStep`), so its rewrite is a
//! definitional change here too, and the pin's simp also reaches it inside the arguments it only
//! `dsimp`s (`congrArgs`, `Types.lean:649-679`: a type argument with forward dependencies, so
//! `@Eq (Fin (2+3)) a b` becomes `@Eq (Fin 5) a b`), never inside an instance or a proof. Every
//! other rewrite carries the pin's proof term, which only the kernel checks: the offsets the
//! procedures read are the lemmas' sides definitionally, not syntactically (`reduceNatEqExpr`'s
//! own "TODO: These proofs rely too much on definitional equality"), so a wrong rewrite is a
//! kernel rejection, never a proof.
//!
//! An exponent above `exponentiation.threshold`'s default makes `Nat.reducePow` warn and leave the
//! power (`checkExponent`, `src/Lean/Util/SafeExponentiation.lean:29-36`). This engine logs no
//! warnings, so that case is a typed refusal rather than a silent difference.
use super::arith::{
    apply, big, constant, eager_refl_bool_true, equation, is_constant, is_heterogeneous_instance,
    name, nat_add, nat_binary, nat_eq, nat_le, nat_literal, nat_type,
};
use super::*;
use crate::source::instances::nonmatch;
use fln_bignum::nat::BigNat;

/// `exponentiation.threshold`'s default, read by `Nat.reducePow`'s `checkExponent`.
const EXPONENT_THRESHOLD: u64 = 256;

/// One of the pin's default `Nat` procedures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NatSimproc {
    Succ,
    Add,
    Mul,
    Sub,
    Div,
    Mod,
    Pow,
    And,
    Xor,
    Or,
    ShiftLeft,
    ShiftRight,
    Gcd,
    Lt,
    Gt,
    BEq,
    BNe,
    EqDiff,
    BeqDiff,
    BneDiff,
    LeDiff,
    SubDiff,
    Dvd,
}

/// Each procedure with its declaration name, in the enumeration's order.
const PROCEDURES: [(NatSimproc, &str); 23] = [
    (NatSimproc::Succ, "Nat.reduceSucc"),
    (NatSimproc::Add, "Nat.reduceAdd"),
    (NatSimproc::Mul, "Nat.reduceMul"),
    (NatSimproc::Sub, "Nat.reduceSub"),
    (NatSimproc::Div, "Nat.reduceDiv"),
    (NatSimproc::Mod, "Nat.reduceMod"),
    (NatSimproc::Pow, "Nat.reducePow"),
    (NatSimproc::And, "Nat.reduceAnd"),
    (NatSimproc::Xor, "Nat.reduceXor"),
    (NatSimproc::Or, "Nat.reduceOr"),
    (NatSimproc::ShiftLeft, "Nat.reduceShiftLeft"),
    (NatSimproc::ShiftRight, "Nat.reduceShiftRight"),
    (NatSimproc::Gcd, "Nat.reduceGcd"),
    (NatSimproc::Lt, "Nat.reduceLT"),
    (NatSimproc::Gt, "Nat.reduceGT"),
    (NatSimproc::BEq, "Nat.reduceBEq"),
    (NatSimproc::BNe, "Nat.reduceBNe"),
    (NatSimproc::EqDiff, "Nat.reduceEqDiff"),
    (NatSimproc::BeqDiff, "Nat.reduceBeqDiff"),
    (NatSimproc::BneDiff, "Nat.reduceBneDiff"),
    (NatSimproc::LeDiff, "Nat.reduceLeDiff"),
    (NatSimproc::SubDiff, "Nat.reduceSubDiff"),
    (NatSimproc::Dvd, "Nat.reduceDvd"),
];

/// The declarations every procedure's result or proof is built from, all in `Init.Prelude`. An
/// environment lacking one (the source seed) runs none of them.
const BUILDING_BLOCKS: &[&str] = &[
    "Nat",
    "OfNat.ofNat",
    "instOfNatNat",
    "HAdd.hAdd",
    "instHAdd",
    "instAddNat",
    "HSub.hSub",
    "instHSub",
    "instSubNat",
    "LE.le",
    "instLENat",
    "LT.lt",
    "instLTNat",
    "BEq.beq",
    "bne",
    "instBEqOfDecidableEq",
    "instDecidableEqNat",
    "Bool",
    "Bool.true",
    "Bool.false",
    "Eq",
    "Eq.refl",
    "True",
    "False",
    "Decidable.decide",
    "of_decide_eq_true",
];

impl NatSimproc {
    fn bit(self) -> u32 {
        1 << self as u32
    }

    /// The procedure the declaration `declaration` names.
    pub(super) fn named(declaration: &Name) -> Option<Self> {
        PROCEDURES
            .iter()
            .find(|(_, text)| *declaration == name(text))
            .map(|(procedure, _)| *procedure)
    }

    /// A `dsimproc`: it runs where `dsimp` runs, and its result has no proof.
    fn definitional(self) -> bool {
        !matches!(
            self,
            Self::Lt
                | Self::Gt
                | Self::EqDiff
                | Self::BeqDiff
                | Self::BneDiff
                | Self::LeDiff
                | Self::SubDiff
                | Self::Dvd
        )
    }
}

/// The procedures one call runs, as its `SimprocsArray` holds them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(in crate::source) struct NatSimprocs(u32);

impl NatSimprocs {
    /// The default set: every procedure (`Simp.getSimprocs`).
    pub(super) fn all() -> Self {
        Self(
            PROCEDURES
                .iter()
                .fold(0, |bits, (procedure, _)| bits | procedure.bit()),
        )
    }

    pub(super) fn contains(self, procedure: NatSimproc) -> bool {
        self.0 & procedure.bit() != 0
    }

    pub(super) fn insert(&mut self, procedure: NatSimproc) {
        self.0 |= procedure.bit();
    }

    pub(super) fn remove(&mut self, procedure: NatSimproc) {
        self.0 &= !procedure.bit();
    }

    pub(super) fn is_empty(self) -> bool {
        self.0 == 0
    }
}

/// How the pin proves a procedure's rewrite. It is built only for the rewrite this engine takes,
/// so a candidate never searches for instances.
#[derive(Clone)]
enum Proof {
    /// None: a `dsimproc`'s result, or a `.done` result without a proof, both of which the pin
    /// leaves definitional.
    Definitional,
    /// `mkEqRefl` of the result (`reduceSubDiff` of two numerals).
    Reflexive,
    /// `evalPropStep` (`Util.lean:20-26`), and `reduceEqDiff`'s `.decide`: `eq_true_of_decide`
    /// or `eq_false_of_decide` at the proposition, its `Decidable` instance and `Eq.refl`.
    Decide { proposition: Expr, value: bool },
    /// `mkAppN (mkConst lemma) args` (`applySimprocConst`, `applyEqLemma`).
    Lemma {
        lemma: &'static str,
        arguments: Vec<Argument>,
    },
}

#[derive(Clone)]
enum Argument {
    Term(Expr),
    /// `mkOfDecideEqTrue p`: `of_decide_eq_true p inst (Eq.refl true)`.
    OfDecide(Expr),
    /// The `Nat.Simproc` proof a `BEq` lemma lifts (`beqEqOfEqEq`, `bneTrueOfEqFalse`, …).
    Proof(Box<Proof>),
}

/// A procedure's rewrite of one node: its result and how the pin proves it.
pub(super) struct ProcedureStep {
    replacement: Expr,
    proof: Proof,
    /// The type of the node and its result: `Nat`, `Bool` or `Prop`.
    carrier: Expr,
}

/// `NatOffset` (`Nat.lean:89-94`): a numeral, or `base + n` with `offset` the numeral `n`.
enum Offset {
    Const(BigNat),
    Offset {
        base: Expr,
        offset: Expr,
        value: BigNat,
    },
}

/// `EqResult` (`Nat.lean:182-185`).
enum EqResult {
    Decide(bool),
    False(Proof),
    Eq(Expr, Expr, Proof),
}

/// Where the pin's simp reaches a subterm: rewriting it (`simp`), or only reducing it
/// definitionally (`dsimp`, in an argument with forward dependencies or a binder's domain).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Visit {
    Simp,
    Dsimp,
}

/// `e.consumeMData`, and the `let _ : T := e; _` this elaborator keeps for a source ascription
/// `(e : T)`: the pin elaborates `(10 : Nat)` to the numeral alone, which its procedures read.
fn without_metadata(mut e: &Expr) -> &Expr {
    loop {
        match e.node() {
            ExprNode::MData { expr, .. } => e = expr,
            ExprNode::LetE { value, .. } if super::super::matching::is_ascription(e) => e = value,
            _ => return e,
        }
    }
}

/// `e.isAppOfArity head arity`, with the arguments: the head is the constant itself, not
/// annotated.
fn application<'e>(e: &'e Expr, head: &str, arity: usize) -> Option<Vec<&'e Expr>> {
    let mut f = e;
    let mut args = Vec::new();
    while let ExprNode::App { f: g, a } = f.node() {
        args.push(a);
        f = g;
    }
    let ExprNode::Const { name: found, .. } = f.node() else {
        return None;
    };
    if args.len() != arity || *found != name(head) {
        return None;
    }
    args.reverse();
    Some(args)
}

fn literal(n: BigNat) -> Expr {
    nat_literal(&n)
}

/// `mkSubNat`.
fn nat_sub(a: Expr, b: Expr) -> Expr {
    nat_binary("instHSub", "HSub.hSub", "instSubNat", a, b)
}

/// `mkLTNat`.
fn nat_lt(a: Expr, b: Expr) -> Expr {
    apply(
        Expr::const_(name("LT.lt"), vec![Level::zero()]),
        [nat_type(), constant("instLTNat"), a, b],
    )
}

/// `mkGTNat`: `y < x`.
fn nat_gt(a: Expr, b: Expr) -> Expr {
    nat_lt(b, a)
}

/// `mkGENat`: `y ≤ x`.
fn nat_ge(a: Expr, b: Expr) -> Expr {
    nat_le(b, a)
}

/// `mkBEqNatInstance`.
fn nat_beq_instance() -> Expr {
    apply(
        Expr::const_(name("instBEqOfDecidableEq"), vec![Level::zero()]),
        [nat_type(), constant("instDecidableEqNat")],
    )
}

/// `mkBEqNat`, or `mkBneNat` when `negated`.
fn nat_beq(negated: bool, a: Expr, b: Expr) -> Expr {
    apply(
        Expr::const_(
            name(if negated { "bne" } else { "BEq.beq" }),
            vec![Level::zero()],
        ),
        [nat_type(), nat_beq_instance(), a, b],
    )
}

fn boolean(value: bool) -> Expr {
    constant(if value { "Bool.true" } else { "Bool.false" })
}

fn truth(value: bool) -> Expr {
    constant(if value { "True" } else { "False" })
}

fn proposition() -> Expr {
    Expr::sort(Level::zero())
}

/// `@Eq.refl.{1} carrier term`.
fn reflexivity(carrier: Expr, term: Expr) -> Expr {
    apply(
        Expr::const_(name("Eq.refl"), vec![Level::one()]),
        [carrier, term],
    )
}

fn nat_step(value: BigNat) -> ProcedureStep {
    ProcedureStep {
        replacement: literal(value),
        proof: Proof::Definitional,
        carrier: nat_type(),
    }
}

fn lemma(lemma: &'static str, arguments: Vec<Argument>) -> Proof {
    Proof::Lemma { lemma, arguments }
}

fn term(e: &Expr) -> Argument {
    Argument::Term(e.clone())
}

impl Context {
    /// Whether this environment declares every procedure's building blocks.
    pub(super) fn simp_procedures_supported(&self) -> bool {
        BUILDING_BLOCKS
            .iter()
            .all(|text| self.txn.env.contains(&name(text)))
    }

    /// The procedure a simp argument `identifier` names, as the pin's `resolveSimpIdTheorem?`
    /// and `elabSimpArg` read one: a declaration it resolves to that is a procedure (under
    /// `import Lean` they are declarations), or, unresolved, a builtin procedure's own name
    /// (`isBuiltinSimproc`). A local is never one.
    pub(super) fn simp_procedure_argument(
        &mut self,
        identifier: &Name,
    ) -> Result<Option<NatSimproc>, NatDefinitionElabError> {
        let mut head = identifier.clone();
        while !head.parent().is_anonymous() {
            head = head.parent();
        }
        if self.txn.lctx.find_by_user_name(identifier).is_some()
            || self.txn.lctx.find_by_user_name(&head).is_some()
        {
            return Ok(None);
        }
        match self.resolve_source_name(identifier) {
            Ok(Some(resolved)) => Ok(NatSimproc::named(&resolved)),
            Ok(None) => Ok(NatSimproc::named(&identifier.erase_macro_scopes())),
            // An ambiguous name is the theorem path's to report.
            Err(_) => Ok(None),
        }
    }

    /// The procedures' rewrite of `target` as evidence `node = result`, with its node: the first
    /// node, children before parents, that a procedure of `set` rewrites. Only closed nodes are
    /// candidates; one under a binder that mentions it is reached by the binder walk.
    pub(super) fn simp_procedure_evidence(
        &mut self,
        target: &Expr,
        set: NatSimprocs,
    ) -> Result<Option<(Typed, Expr)>, NatDefinitionElabError> {
        let Some((node, step)) = self.simp_procedure_step(target, set)? else {
            return Ok(None);
        };
        let value = match &step.proof {
            Proof::Definitional => reflexivity(step.carrier.clone(), node.clone()),
            Proof::Reflexive => reflexivity(step.carrier.clone(), step.replacement.clone()),
            proof => self.simp_procedure_proof(proof)?,
        };
        let type_ = equation(step.carrier, node.clone(), step.replacement);
        Ok(Some((Typed { value, type_ }, node)))
    }

    /// The procedures' first rewrite of `target` when it is definitional: `target` with the node
    /// replaced at every position the pin's simp or `dsimp` reaches. `NotDefinition` otherwise,
    /// leaving the rewrite to [`Self::simp_procedure_evidence`]. Once an earlier rule has chosen
    /// a rewrite (ordered rewriting), the procedures, which run after every theorem, have none.
    pub(super) fn simp_procedure_unfold(
        &mut self,
        target: &Expr,
        set: NatSimprocs,
    ) -> Result<UnfoldResult, NatDefinitionElabError> {
        if self.simp_reach_limit.is_some() {
            return Ok(UnfoldResult::NotDefinition);
        }
        match self.simp_procedure_step(target, set)? {
            Some((node, step)) if matches!(step.proof, Proof::Definitional) => {
                Ok(UnfoldResult::Changed(self.simp_procedure_replace(
                    target,
                    &node,
                    &step.replacement,
                )?))
            }
            _ => Ok(UnfoldResult::NotDefinition),
        }
    }

    /// The `dsimproc`s' rewrite of `term` itself, as `dsimp`'s `dpost` runs them
    /// (`dpostDefault`, `Rewrite.lean:417-419`), or `None`.
    pub(super) fn dsimp_procedure(
        &mut self,
        term: &Expr,
        set: NatSimprocs,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if set.is_empty() || term.has_loose_bvars() {
            return Ok(None);
        }
        Ok(self
            .simp_procedure_at(term, set, Visit::Dsimp)?
            .map(|step| step.replacement))
    }

    /// The first node, children before parents, at which a procedure of `set` rewrites, and that
    /// rewrite. A node reached only by `dsimp` admits only the `dsimproc`s.
    fn simp_procedure_step(
        &mut self,
        target: &Expr,
        set: NatSimprocs,
    ) -> Result<Option<(Expr, ProcedureStep)>, NatDefinitionElabError> {
        // (term, how it is reached, children pushed)
        let mut stack: Vec<(&Expr, Visit, bool)> = vec![(target, Visit::Simp, false)];
        let mut seen = HashSet::new();
        while let Some((term, visit, expanded)) = stack.pop() {
            self.tick()?;
            if !expanded {
                if !seen.insert((term.allocation_identity(), visit)) {
                    continue;
                }
                stack.push((term, visit, true));
                for (child, reach) in self.simp_procedure_children(term, visit).into_iter().rev() {
                    stack.push((child, reach, false));
                }
                continue;
            }
            // Simp visits an annotation's expression, never the annotation itself.
            if term.has_loose_bvars() || matches!(term.node(), ExprNode::MData { .. }) {
                continue;
            }
            if let Some(step) = self.simp_procedure_at(term, set, visit)? {
                return Ok(Some((term.clone(), step)));
            }
        }
        Ok(None)
    }

    /// The subterms of `term` the pin's simp reaches, each with how: an application's `eq`
    /// arguments are simplified and its other explicit data arguments only `dsimp`ed
    /// (`congrArgs`, `Types.lean:649-679`), never an instance (`skipInstances`) or a proof
    /// (`doNotVisitProofs`); a binder's body is simplified and a dependent binder's domain
    /// `dsimp`ed (`simpForall`, `lambdaTelescopeDSimp`). Under `dsimp` every one of them is
    /// `dsimp`ed. A head whose type is unknown has every part reached.
    fn simp_procedure_children<'e>(&self, term: &'e Expr, visit: Visit) -> Vec<(&'e Expr, Visit)> {
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
                    let mut all = vec![(head, visit)];
                    all.extend(args.into_iter().map(|arg| (arg, visit)));
                    return all;
                };
                let rewritten = self.simp_arith_argument_kinds(&type_, args.len());
                let mut binders: Vec<(&Expr, BinderInfo)> = Vec::new();
                let mut rest = &type_;
                let mut children = Vec::new();
                for (index, arg) in args.into_iter().enumerate() {
                    let binder = match rest.node() {
                        ExprNode::ForallE {
                            binder_type,
                            body,
                            binder_info,
                            ..
                        } => {
                            rest = body;
                            Some((binder_type, *binder_info))
                        }
                        _ => None,
                    };
                    let reach = match binder {
                        // Past the declared telescope: simplified, as `congrArgs` does an
                        // argument of an arrow.
                        None => Some(visit),
                        Some((_, BinderInfo::InstImplicit)) => None,
                        Some(_) if rewritten[index] => Some(visit),
                        Some((binder_type, _))
                            if self.simp_arith_is_proof_type(binder_type, &binders) =>
                        {
                            None
                        }
                        Some(_) => Some(Visit::Dsimp),
                    };
                    if let Some(binder) = binder {
                        binders.push(binder);
                    }
                    if let Some(reach) = reach {
                        children.push((arg, reach));
                    }
                }
                children
            }
            ExprNode::Lam {
                binder_type, body, ..
            } => vec![(binder_type, Visit::Dsimp), (body, visit)],
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                let domain = if body.has_loose_bvar(0) {
                    Visit::Dsimp
                } else {
                    visit
                };
                vec![(binder_type, domain), (body, visit)]
            }
            ExprNode::LetE { value, body, .. } => vec![(value, visit), (body, visit)],
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => vec![(expr, visit)],
            _ => Vec::new(),
        }
    }

    /// `target` with `node` replaced by `replacement` at every position
    /// [`Self::simp_procedure_children`] reaches; the rest keeps its form.
    fn simp_procedure_replace(
        &mut self,
        target: &Expr,
        node: &Expr,
        replacement: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut done: HashMap<usize, Expr> = HashMap::new();
        // Every visited term stays alive, so an allocation identity is never reused.
        let mut retained = Vec::new();
        let mut work = vec![(target.clone(), false)];
        while let Some((term, exit)) = work.pop() {
            self.tick()?;
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            if !exit {
                if self.rewrite_same(&term, node)? {
                    done.insert(key, replacement.clone());
                    retained.push(term);
                    continue;
                }
                let children: Vec<Expr> = self
                    .simp_procedure_children(&term, Visit::Simp)
                    .into_iter()
                    .map(|(child, _)| child.clone())
                    .collect();
                work.push((term.clone(), true));
                work.extend(children.into_iter().map(|child| (child, false)));
                continue;
            }
            // The positions reached, as the references `simp_procedure_children` hands back into
            // `term` itself: one subterm may be reached at one position and not at another.
            let reached: Vec<*const Expr> = self
                .simp_procedure_children(&term, Visit::Simp)
                .into_iter()
                .map(|(child, _)| child as *const Expr)
                .collect();
            let at = |child: &Expr| -> Expr {
                if reached.contains(&(child as *const Expr)) {
                    done[&child.allocation_identity()].clone()
                } else {
                    child.clone()
                }
            };
            let rebuilt = match term.node() {
                ExprNode::App { .. } => {
                    let mut head = &term;
                    let mut args = Vec::new();
                    while let ExprNode::App { f, a } = head.node() {
                        args.push(a);
                        head = f;
                    }
                    args.into_iter()
                        .rev()
                        .fold(at(head), |f, arg| Expr::app(f, at(arg)))
                }
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(binder_name.clone(), at(binder_type), at(body), *binder_info),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(binder_name.clone(), at(binder_type), at(body), *binder_info),
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    non_dep,
                } => Expr::let_e(
                    decl_name.clone(),
                    type_.clone(),
                    at(value),
                    at(body),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), at(expr)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, at(expr)),
                _ => term.clone(),
            };
            let unchanged = self.rewrite_same(&rebuilt, &term)?;
            done.insert(key, if unchanged { term.clone() } else { rebuilt });
            retained.push(term);
        }
        Ok(done
            .remove(&target.allocation_identity())
            .expect("the replacement finishes its root"))
    }

    /// The first procedure of `set` that rewrites `node`, in the order the pin's discrimination
    /// tree returns the candidates for its key; a node reached only by `dsimp` admits only the
    /// `dsimproc`s. A procedure whose proof names a declaration the environment lacks does not
    /// fire, as `applySimprocConst` and `applyEqLemma` decline then (the pin builds the other
    /// proofs regardless; only an environment without `Init`'s lemmas lacks them).
    fn simp_procedure_at(
        &mut self,
        node: &Expr,
        set: NatSimprocs,
        visit: Visit,
    ) -> Result<Option<ProcedureStep>, NatDefinitionElabError> {
        use NatSimproc::*;
        let mut head = node;
        let mut args = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        args.reverse();
        let ExprNode::Const { name: head, .. } = head.node() else {
            return Ok(None);
        };
        // The keys' type arguments: `Nat`, read as the discrimination tree reads them.
        let nat = |count: usize| {
            args.len() > count && args[..count].iter().all(|a| is_constant(a, "Nat"))
        };
        let candidates: &[NatSimproc] = match (head.to_display_string().as_str(), args.len()) {
            ("Nat.succ", 1) => &[Succ],
            ("Nat.gcd", 2) => &[Gcd],
            ("HAdd.hAdd", 6) if nat(3) => &[Add],
            ("HMul.hMul", 6) if nat(3) => &[Mul],
            ("HSub.hSub", 6) if nat(3) => &[Sub, SubDiff],
            ("HDiv.hDiv", 6) if nat(3) => &[Div],
            ("HMod.hMod", 6) if nat(3) => &[Mod],
            ("HPow.hPow", 6) if nat(3) => &[Pow],
            ("HAnd.hAnd", 6) if nat(3) => &[And],
            ("HXor.hXor", 6) if nat(3) => &[Xor],
            ("HOr.hOr", 6) if nat(3) => &[Or],
            ("HShiftLeft.hShiftLeft", 6) if nat(3) => &[ShiftLeft],
            ("HShiftRight.hShiftRight", 6) if nat(3) => &[ShiftRight],
            ("LT.lt", 4) if nat(1) => &[Lt],
            ("GT.gt", 4) if nat(1) => &[Gt],
            ("BEq.beq", 4) if nat(1) => &[BEq, BeqDiff],
            ("bne", 4) if nat(1) => &[BNe, BneDiff],
            ("Eq", 3) if nat(1) => &[EqDiff],
            ("LE.le", 4) if nat(1) => &[LeDiff],
            ("Dvd.dvd", 4) if nat(1) => &[Dvd],
            _ => &[],
        };
        for &procedure in candidates {
            if !set.contains(procedure) || (visit == Visit::Dsimp && !procedure.definitional()) {
                continue;
            }
            self.tick()?;
            if let Some(step) = self.simp_procedure(procedure, node, &args)?
                && self.simp_procedure_declared(&step.proof)
            {
                return Ok(Some(step));
            }
        }
        Ok(None)
    }

    /// Whether the environment declares the lemmas `proof` names.
    fn simp_procedure_declared(&self, proof: &Proof) -> bool {
        let mut pending = vec![proof];
        while let Some(proof) = pending.pop() {
            match proof {
                Proof::Definitional | Proof::Reflexive => {}
                Proof::Decide { value, .. } => {
                    let lemma = if *value {
                        "eq_true_of_decide"
                    } else {
                        "eq_false_of_decide"
                    };
                    if !self.txn.env.contains(&name(lemma)) {
                        return false;
                    }
                }
                Proof::Lemma { lemma, arguments } => {
                    if !self.txn.env.contains(&name(lemma)) {
                        return false;
                    }
                    for argument in arguments {
                        if let Argument::Proof(inner) = argument {
                            pending.push(inner);
                        }
                    }
                }
            }
        }
        true
    }

    /// One procedure at `node`, whose arguments are `args`.
    fn simp_procedure(
        &mut self,
        procedure: NatSimproc,
        node: &Expr,
        args: &[&Expr],
    ) -> Result<Option<ProcedureStep>, NatDefinitionElabError> {
        use NatSimproc::*;
        match procedure {
            // `reduceUnary` (`Nat.lean:22-25`).
            Succ => Ok(self
                .simp_procedure_literal(args[0])?
                .map(|n| nat_step(n.add(&BigNat::from_u64(1))))),
            // `reduceBin` (`Nat.lean:27-31`), `reducePow` (`:58-64`) and `reduceGcd` (`:76`).
            Add | Mul | Sub | Div | Mod | Pow | And | Xor | Or | ShiftLeft | ShiftRight | Gcd => {
                let (left, right) = if procedure == Gcd {
                    (args[0], args[1])
                } else {
                    (args[4], args[5])
                };
                let Some(n) = self.simp_procedure_literal(left)? else {
                    return Ok(None);
                };
                let Some(m) = self.simp_procedure_literal(right)? else {
                    return Ok(None);
                };
                let resource = || failure(SourceInferenceError::ResourceLimit);
                let value = match procedure {
                    Add => n.add(&m),
                    Mul => n.mul(&m),
                    Sub => n.sub(&m),
                    Div => n.div(&m),
                    Mod => n.rem(&m),
                    And => n.land(&m),
                    Xor => n.lxor(&m),
                    Or => n.lor(&m),
                    Gcd => n.gcd(&m),
                    ShiftLeft => {
                        let bits = m.to_u64().ok_or_else(resource)?;
                        n.checked_shl(bits).ok_or_else(resource)?
                    }
                    // A shift past every bit leaves zero.
                    ShiftRight => match m.to_u64() {
                        Some(bits) => n.shr(bits),
                        None => BigNat::zero(),
                    },
                    _ => {
                        if m > BigNat::from_u64(EXPONENT_THRESHOLD) {
                            return Err(error(TacticError::SimprocUnsupported(
                                "`Nat.reducePow` at an exponent above `exponentiation.threshold`, where the pin warns",
                            )));
                        }
                        let exponent = m.to_u64().and_then(|m| u32::try_from(m).ok());
                        n.checked_pow(exponent.ok_or_else(resource)?)
                            .ok_or_else(resource)?
                    }
                };
                Ok(Some(nat_step(value)))
            }
            // `reduceBinPred` (`Nat.lean:33-37`) with `evalPropStep`.
            Lt | Gt => {
                let Some(n) = self.simp_procedure_literal(args[2])? else {
                    return Ok(None);
                };
                let Some(m) = self.simp_procedure_literal(args[3])? else {
                    return Ok(None);
                };
                let value = if procedure == Lt { n < m } else { n > m };
                Ok(Some(ProcedureStep {
                    replacement: truth(value),
                    proof: Proof::Decide {
                        proposition: node.clone(),
                        value,
                    },
                    carrier: proposition(),
                }))
            }
            // `reduceBoolPred` (`Nat.lean:39-43`).
            BEq | BNe => {
                let Some(n) = self.simp_procedure_literal(args[2])? else {
                    return Ok(None);
                };
                let Some(m) = self.simp_procedure_literal(args[3])? else {
                    return Ok(None);
                };
                Ok(Some(ProcedureStep {
                    replacement: boolean((n == m) != (procedure == BNe)),
                    proof: Proof::Definitional,
                    carrier: constant("Bool"),
                }))
            }
            // `reduceEqDiff` (`Nat.lean:228-247`).
            EqDiff => Ok(match self.simp_procedure_nat_eq(args[1], args[2])? {
                None => None,
                Some(EqResult::Decide(value)) => Some(ProcedureStep {
                    replacement: truth(value),
                    proof: Proof::Decide {
                        proposition: node.clone(),
                        value,
                    },
                    carrier: proposition(),
                }),
                Some(EqResult::False(proof)) => Some(ProcedureStep {
                    replacement: truth(false),
                    proof,
                    carrier: proposition(),
                }),
                Some(EqResult::Eq(x, y, proof)) => Some(ProcedureStep {
                    replacement: nat_eq(x, y),
                    proof,
                    carrier: proposition(),
                }),
            }),
            // `reduceBeqDiff` and `reduceBneDiff` (`Nat.lean:249-281`).
            BeqDiff | BneDiff => {
                let negated = procedure == BneDiff;
                let (x, y) = (args[2], args[3]);
                let (lifted, falsified) = if negated {
                    ("Nat.Simproc.bneEqOfEqEq", "Nat.Simproc.bneTrueOfEqFalse")
                } else {
                    ("Nat.Simproc.beqEqOfEqEq", "Nat.Simproc.beqFalseOfEqFalse")
                };
                Ok(match self.simp_procedure_nat_eq(x, y)? {
                    None => None,
                    Some(EqResult::Decide(value)) => Some(ProcedureStep {
                        replacement: boolean(value != negated),
                        proof: Proof::Definitional,
                        carrier: constant("Bool"),
                    }),
                    Some(EqResult::False(proof)) => Some(ProcedureStep {
                        replacement: boolean(negated),
                        proof: lemma(
                            falsified,
                            vec![term(x), term(y), Argument::Proof(Box::new(proof))],
                        ),
                        carrier: constant("Bool"),
                    }),
                    Some(EqResult::Eq(u, v, proof)) => Some(ProcedureStep {
                        replacement: nat_beq(negated, u.clone(), v.clone()),
                        proof: lemma(
                            lifted,
                            vec![
                                term(x),
                                term(y),
                                Argument::Term(u),
                                Argument::Term(v),
                                Argument::Proof(Box::new(proof)),
                            ],
                        ),
                        carrier: constant("Bool"),
                    }),
                })
            }
            LeDiff => self.simp_procedure_le(node, args[2], args[3]),
            SubDiff => self.simp_procedure_sub(args[4], args[5]),
            // `reduceDvd` (`Nat.lean:356-364`).
            Dvd => {
                let instance = Expr::const_(name("Nat.instDvd"), Vec::new());
                if !self.simp_procedure_instance(args[1], &instance)? {
                    return Ok(None);
                }
                let Some(a) = self.simp_procedure_literal(args[2])? else {
                    return Ok(None);
                };
                let Some(b) = self.simp_procedure_literal(args[3])? else {
                    return Ok(None);
                };
                let divides = b.rem(&a).is_zero();
                let lemma_name = if divides {
                    "Nat.dvd_eq_true_of_mod_eq_zero"
                } else {
                    "Nat.dvd_eq_false_of_mod_ne_zero"
                };
                Ok(Some(ProcedureStep {
                    replacement: truth(divides),
                    proof: lemma(
                        lemma_name,
                        vec![
                            term(args[2]),
                            term(args[3]),
                            Argument::Term(eager_refl_bool_true()),
                        ],
                    ),
                    carrier: proposition(),
                }))
            }
        }
    }

    /// `Nat.fromExpr?` (`getNatValue?`, `src/Lean/Meta/LitValues.lean:36-41`): a raw numeral, or
    /// `OfNat.ofNat α n _` of a raw numeral `n` where `α` reduces to `Nat`.
    fn simp_procedure_literal(
        &mut self,
        e: &Expr,
    ) -> Result<Option<BigNat>, NatDefinitionElabError> {
        let e = without_metadata(e);
        if let ExprNode::Lit {
            literal: Literal::Nat(n),
        } = e.node()
        {
            return Ok(Some(big(n)));
        }
        let Some(args) = application(e, "OfNat.ofNat", 3) else {
            return Ok(None);
        };
        let ExprNode::Lit {
            literal: Literal::Nat(n),
        } = without_metadata(args[1]).node()
        else {
            return Ok(None);
        };
        let n = big(n);
        if is_constant(args[0], "Nat") {
            return Ok(Some(n));
        }
        if args[0].has_loose_bvars() || args[0].has_expr_mvar() {
            return Ok(None);
        }
        let type_ = self.whnf(args[0])?;
        let mut head = &type_;
        while let ExprNode::App { f, .. } = head.node() {
            head = f;
        }
        Ok(is_constant(head, "Nat").then_some(n))
    }

    /// `matchesInstance` (`src/Lean/Meta/Offset.lean:70-72`): `instance` is `expected` at
    /// instance transparency, assigning nothing.
    fn simp_procedure_instance(
        &mut self,
        instance: &Expr,
        expected: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if self.rewrite_same(instance, expected)? {
            return Ok(true);
        }
        if instance.has_expr_mvar() || instance.has_level_mvar() || instance.has_loose_bvars() {
            return Ok(false);
        }
        let mut trial = self.rewrite_trial();
        let mut budget = UnificationBudget::new(trial.kernel);
        budget.transparency = UnificationTransparency::Instances;
        let matched = trial.proof_types_match_with_budget(instance, expected, budget);
        self.charge_rewrite_trial(&trial);
        match matched {
            Ok(matched) => Ok(matched),
            Err(problem) if nonmatch(&problem) => Ok(false),
            Err(problem) => Err(problem),
        }
    }

    /// `NatOffset.asOffset` (`Nat.lean:96-118`): `base + n` for a numeral `n`, through `HAdd`
    /// and `Add` at `Nat`'s instances, `Nat.add` or `Nat.succ`.
    fn simp_procedure_as_offset(
        &mut self,
        e: &Expr,
    ) -> Result<Option<(Expr, BigNat)>, NatDefinitionElabError> {
        if let Some(args) = application(e, "HAdd.hAdd", 6) {
            if !is_heterogeneous_instance(args[3], "instHAdd", "instAddNat") {
                let expected = apply(
                    Expr::const_(name("instHAdd"), vec![Level::zero()]),
                    [nat_type(), constant("instAddNat")],
                );
                if !self.simp_procedure_instance(args[3], &expected)? {
                    return Ok(None);
                }
            }
            return Ok(self
                .simp_procedure_literal(args[5])?
                .map(|n| (args[4].clone(), n)));
        }
        if let Some(args) = application(e, "Add.add", 4) {
            if !self.simp_procedure_instance(args[1], &constant("instAddNat"))? {
                return Ok(None);
            }
            return Ok(self
                .simp_procedure_literal(args[3])?
                .map(|n| (args[2].clone(), n)));
        }
        if let Some(args) = application(e, "Nat.add", 2) {
            return Ok(self
                .simp_procedure_literal(args[1])?
                .map(|n| (args[0].clone(), n)));
        }
        if let Some(args) = application(e, "Nat.succ", 1) {
            return Ok(Some((args[0].clone(), BigNat::from_u64(1))));
        }
        Ok(None)
    }

    /// `NatOffset.fromExpr?` (`Nat.lean:121-136`): a numeral, or the base its offsets are
    /// peeled from with their sum.
    fn simp_procedure_offset(
        &mut self,
        e: &Expr,
    ) -> Result<Option<Offset>, NatDefinitionElabError> {
        if let Some(n) = self.simp_procedure_literal(e)? {
            return Ok(Some(Offset::Const(n)));
        }
        // `fromExprAux`, its recursion as a loop: each step peels a strictly smaller base.
        let mut base = without_metadata(e).clone();
        let mut total = BigNat::zero();
        while let Some((next, n)) = self.simp_procedure_as_offset(&base)? {
            self.tick()?;
            total = total.add(&n);
            base = without_metadata(&next).clone();
        }
        if total.is_zero() {
            return Ok(None);
        }
        Ok(Some(Offset::Offset {
            base,
            offset: literal(total.clone()),
            value: total,
        }))
    }

    /// `reduceNatEqExpr` (`Nat.lean:192-226`), with `applyEqLemma`'s check that the lemma is
    /// declared left to [`Self::simp_procedure_declared`].
    fn simp_procedure_nat_eq(
        &mut self,
        x: &Expr,
        y: &Expr,
    ) -> Result<Option<EqResult>, NatDefinitionElabError> {
        let Some(left) = self.simp_procedure_offset(x)? else {
            return Ok(None);
        };
        let Some(right) = self.simp_procedure_offset(y)? else {
            return Ok(None);
        };
        Ok(Some(match (left, right) {
            (Offset::Const(xn), Offset::Const(yn)) => EqResult::Decide(xn == yn),
            (
                Offset::Offset {
                    base: xb,
                    offset: xo,
                    value: xn,
                },
                Offset::Const(yn),
            ) => {
                if xn <= yn {
                    EqResult::Eq(
                        xb.clone(),
                        literal(yn.sub(&xn)),
                        lemma(
                            "Nat.Simproc.add_eq_le",
                            vec![
                                term(&xb),
                                term(&xo),
                                term(y),
                                Argument::OfDecide(nat_le(xo, y.clone())),
                            ],
                        ),
                    )
                } else {
                    EqResult::False(lemma(
                        "Nat.Simproc.add_eq_gt",
                        vec![
                            term(&xb),
                            term(&xo),
                            term(y),
                            Argument::OfDecide(nat_gt(xo, y.clone())),
                        ],
                    ))
                }
            }
            (
                Offset::Const(xn),
                Offset::Offset {
                    base: yb,
                    offset: yo,
                    value: yn,
                },
            ) => {
                if yn <= xn {
                    EqResult::Eq(
                        yb.clone(),
                        literal(xn.sub(&yn)),
                        lemma(
                            "Nat.Simproc.eq_add_le",
                            vec![
                                term(x),
                                term(&yb),
                                term(&yo),
                                Argument::OfDecide(nat_le(yo, x.clone())),
                            ],
                        ),
                    )
                } else {
                    EqResult::False(lemma(
                        "Nat.Simproc.eq_add_gt",
                        vec![
                            term(x),
                            term(&yb),
                            term(&yo),
                            Argument::OfDecide(nat_gt(yo, x.clone())),
                        ],
                    ))
                }
            }
            (
                Offset::Offset {
                    base: xb,
                    offset: xo,
                    value: xn,
                },
                Offset::Offset {
                    base: yb,
                    offset: yo,
                    value: yn,
                },
            ) => {
                let arguments = |guard: Expr| {
                    vec![
                        term(&xb),
                        term(&yb),
                        term(&xo),
                        term(&yo),
                        Argument::OfDecide(guard),
                    ]
                };
                if xn <= yn {
                    let zb = if xn == yn {
                        yb.clone()
                    } else {
                        nat_add(yb.clone(), literal(yn.sub(&xn)))
                    };
                    EqResult::Eq(
                        xb.clone(),
                        zb,
                        lemma(
                            "Nat.Simproc.add_eq_add_le",
                            arguments(nat_le(xo.clone(), yo.clone())),
                        ),
                    )
                } else {
                    let zb = nat_add(xb.clone(), literal(xn.sub(&yn)));
                    EqResult::Eq(
                        zb,
                        yb.clone(),
                        lemma(
                            "Nat.Simproc.add_eq_add_ge",
                            arguments(nat_ge(xo.clone(), yo.clone())),
                        ),
                    )
                }
            }
        }))
    }

    /// `reduceLTLE ``LE.le 4 false` (`Nat.lean:283-319`), `Nat.reduceLeDiff`.
    fn simp_procedure_le(
        &mut self,
        node: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Result<Option<ProcedureStep>, NatDefinitionElabError> {
        let Some(left) = self.simp_procedure_offset(x)? else {
            return Ok(None);
        };
        let Some(right) = self.simp_procedure_offset(y)? else {
            return Ok(None);
        };
        let step = |replacement: Expr, proof: Proof| ProcedureStep {
            replacement,
            proof,
            carrier: proposition(),
        };
        Ok(Some(match (left, right) {
            (Offset::Const(xn), Offset::Const(yn)) => {
                let value = xn <= yn;
                step(
                    truth(value),
                    Proof::Decide {
                        proposition: node.clone(),
                        value,
                    },
                )
            }
            (
                Offset::Offset {
                    base: xb,
                    offset: xo,
                    value: xn,
                },
                Offset::Const(yn),
            ) => {
                if xn <= yn {
                    step(
                        nat_le(xb.clone(), literal(yn.sub(&xn))),
                        lemma(
                            "Nat.Simproc.add_le_le",
                            vec![
                                term(&xb),
                                term(&xo),
                                term(y),
                                Argument::OfDecide(nat_le(xo, y.clone())),
                            ],
                        ),
                    )
                } else {
                    step(
                        truth(false),
                        lemma(
                            "Nat.Simproc.add_le_gt",
                            vec![
                                term(&xb),
                                term(&xo),
                                term(y),
                                Argument::OfDecide(nat_gt(xo, y.clone())),
                            ],
                        ),
                    )
                }
            }
            (
                Offset::Const(xn),
                Offset::Offset {
                    base: yb,
                    offset: yo,
                    value: yn,
                },
            ) => {
                if xn <= yn {
                    step(
                        truth(true),
                        lemma(
                            "Nat.Simproc.le_add_le",
                            vec![
                                term(x),
                                term(&yb),
                                term(&yo),
                                Argument::OfDecide(nat_le(x.clone(), yo)),
                            ],
                        ),
                    )
                } else {
                    step(
                        nat_le(literal(xn.sub(&yn)), yb.clone()),
                        lemma(
                            "Nat.Simproc.le_add_ge",
                            vec![
                                term(x),
                                term(&yb),
                                term(&yo),
                                Argument::OfDecide(nat_ge(x.clone(), yo)),
                            ],
                        ),
                    )
                }
            }
            (
                Offset::Offset {
                    base: xb,
                    offset: xo,
                    value: xn,
                },
                Offset::Offset {
                    base: yb,
                    offset: yo,
                    value: yn,
                },
            ) => {
                let arguments = |guard: Expr| {
                    vec![
                        term(&xb),
                        term(&yb),
                        term(&xo),
                        term(&yo),
                        Argument::OfDecide(guard),
                    ]
                };
                if xn <= yn {
                    let right = if xn == yn {
                        yb.clone()
                    } else {
                        nat_add(yb.clone(), literal(yn.sub(&xn)))
                    };
                    step(
                        nat_le(xb.clone(), right),
                        lemma(
                            "Nat.Simproc.add_le_add_le",
                            arguments(nat_le(xo.clone(), yo.clone())),
                        ),
                    )
                } else {
                    step(
                        nat_le(nat_add(xb.clone(), literal(xn.sub(&yn))), yb.clone()),
                        lemma(
                            "Nat.Simproc.add_le_add_ge",
                            arguments(nat_ge(xo.clone(), yo.clone())),
                        ),
                    )
                }
            }
        }))
    }

    /// `Nat.reduceSubDiff` (`Nat.lean:321-354`).
    fn simp_procedure_sub(
        &mut self,
        p: &Expr,
        q: &Expr,
    ) -> Result<Option<ProcedureStep>, NatDefinitionElabError> {
        let Some(left) = self.simp_procedure_offset(p)? else {
            return Ok(None);
        };
        let Some(right) = self.simp_procedure_offset(q)? else {
            return Ok(None);
        };
        let step = |replacement: Expr, proof: Proof| ProcedureStep {
            replacement,
            proof,
            carrier: nat_type(),
        };
        Ok(Some(match (left, right) {
            (Offset::Const(pn), Offset::Const(qn)) => step(literal(pn.sub(&qn)), Proof::Reflexive),
            (
                Offset::Offset {
                    base: pb,
                    offset: po,
                    value: pn,
                },
                Offset::Const(n),
            ) => {
                if pn <= n {
                    let result = if pn == n {
                        pb.clone()
                    } else {
                        nat_sub(pb.clone(), literal(n.sub(&pn)))
                    };
                    step(
                        result,
                        lemma(
                            "Nat.Simproc.add_sub_le",
                            vec![
                                term(&pb),
                                term(&po),
                                term(q),
                                Argument::OfDecide(nat_le(po, q.clone())),
                            ],
                        ),
                    )
                } else {
                    step(
                        nat_add(pb.clone(), literal(pn.sub(&n))),
                        lemma(
                            "Nat.add_sub_assoc",
                            vec![
                                term(&po),
                                term(q),
                                Argument::OfDecide(nat_ge(po.clone(), q.clone())),
                                term(&pb),
                            ],
                        ),
                    )
                }
            }
            (
                Offset::Const(pn),
                Offset::Offset {
                    base: nb,
                    offset: no,
                    value: nn,
                },
            ) => step(
                nat_sub(literal(pn.sub(&nn)), nb.clone()),
                lemma(
                    "Nat.Simproc.sub_add_eq_comm",
                    vec![term(p), term(&nb), term(&no)],
                ),
            ),
            (
                Offset::Offset {
                    base: pb,
                    offset: po,
                    value: pn,
                },
                Offset::Offset {
                    base: nb,
                    offset: no,
                    value: nn,
                },
            ) => {
                let arguments = |guard: Expr| {
                    vec![
                        term(&pb),
                        term(&nb),
                        term(&po),
                        term(&no),
                        Argument::OfDecide(guard),
                    ]
                };
                if pn <= nn {
                    let right = if pn == nn {
                        nb.clone()
                    } else {
                        nat_add(nb.clone(), literal(nn.sub(&pn)))
                    };
                    step(
                        nat_sub(pb.clone(), right),
                        lemma(
                            "Nat.Simproc.add_sub_add_le",
                            arguments(nat_le(po.clone(), no.clone())),
                        ),
                    )
                } else {
                    step(
                        nat_sub(nat_add(pb.clone(), literal(pn.sub(&nn))), nb.clone()),
                        lemma(
                            "Nat.Simproc.add_sub_add_ge",
                            arguments(nat_ge(po.clone(), no.clone())),
                        ),
                    )
                }
            }
        }))
    }

    /// The proof term `proof` describes. A lemma nests a lemma at most once, so this recursion
    /// is two frames deep.
    fn simp_procedure_proof(&mut self, proof: &Proof) -> Result<Expr, NatDefinitionElabError> {
        match proof {
            Proof::Decide { proposition, value } => {
                let instance = self.simp_procedure_decidable(proposition)?;
                let lemma = if *value {
                    "eq_true_of_decide"
                } else {
                    "eq_false_of_decide"
                };
                Ok(apply(
                    constant(lemma),
                    [
                        proposition.clone(),
                        instance,
                        reflexivity(constant("Bool"), boolean(*value)),
                    ],
                ))
            }
            Proof::Lemma { lemma, arguments } => {
                let mut value = constant(lemma);
                for argument in arguments {
                    self.tick()?;
                    let argument = match argument {
                        Argument::Term(e) => e.clone(),
                        Argument::OfDecide(p) => {
                            let instance = self.simp_procedure_decidable(p)?;
                            apply(
                                constant("of_decide_eq_true"),
                                [
                                    p.clone(),
                                    instance,
                                    reflexivity(constant("Bool"), boolean(true)),
                                ],
                            )
                        }
                        Argument::Proof(inner) => self.simp_procedure_proof(inner)?,
                    };
                    value = Expr::app(value, argument);
                }
                Ok(value)
            }
            Proof::Definitional | Proof::Reflexive => Err(error(TacticError::MalformedScript)),
        }
    }

    /// `mkDecide p`'s instance: the `Decidable p` the search finds. The pin's `mkDecide` throws
    /// where there is none, as it does here.
    fn simp_procedure_decidable(&mut self, p: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.simp_decidable_dictionary(p)?.ok_or_else(|| {
            error(TacticError::SimprocUnsupported(
                "a proposition whose `Decidable` instance the search does not find",
            ))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn procedures_are_named_in_the_enumerations_order() {
        for (index, (procedure, text)) in PROCEDURES.iter().enumerate() {
            assert_eq!(*procedure as usize, index, "{text}");
            assert_eq!(NatSimproc::named(&name(text)), Some(*procedure));
        }
        assert_eq!(NatSimproc::named(&name("Nat.reduceIte")), None);
        let mut set = NatSimprocs::default();
        assert!(set.is_empty());
        set.insert(NatSimproc::Add);
        assert!(set.contains(NatSimproc::Add) && !set.contains(NatSimproc::Mul));
        let mut all = NatSimprocs::all();
        all.remove(NatSimproc::Dvd);
        assert!(!all.contains(NatSimproc::Dvd) && all.contains(NatSimproc::Succ));
    }
}
