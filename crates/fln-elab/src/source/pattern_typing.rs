//! The pin's typing of `match` patterns, replayed before the match is lowered (bead
//! `franken_lean-z8j.1.6.3`; vendored `src/Lean/Elab/Match.lean`).
//!
//! The pin elaborates each alternative's patterns as terms, left to right, against the match
//! type (`elabPatterns`). A named pattern variable is a local that unification cannot assign;
//! `_`, a `?x` hole and an implicit constructor argument are natural metavariables it can
//! (`BuiltinTerm.lean:65`, under `inPattern`). A constructor's explicit arguments are elaborated
//! against its binder types before its own type meets the expected one, which is propagated first
//! only when the result type depends on no remaining argument (`App.lean`,
//! `getResultingTypeCore?`). When a top-level pattern's type does not unify, the pattern is
//! elaborated again against the discriminant type with its indices erased, and the match is
//! refined only along a path that reaches a free variable through applications of one constructor
//! (`findDiscrRefinementPath`): the index at that path in the discriminant's own type becomes a
//! new discriminant with a hole pattern (`getIndexToInclude?`, `elabMatchAltViews`), unless it
//! already is one. Otherwise the first error stands. A nested pattern is never refined.
//!
//! FrankenLean's own lowering solves index equations the pin leaves alone, so it admitted matches
//! the pin refuses: `.cons k x _` against `Vec Nat 2` (`k + 1 =?= 2` with `k` rigid, and no path
//! from a literal), or `.cons k x .nil` against `Vec Nat n` (a nested `Vec.nil` against
//! `Vec Nat k`). This module replays the pin's decision on a model whose definitional equality
//! answers yes, no or unknown, and refuses a match only when every step of that decision was
//! decided. A form it does not model (a literal of another type, an anonymous constructor, a
//! definition to unfold, a let-bound local) leaves the match to the lowering as before, so a match
//! the pin admits is never refused here; universe levels are not compared, which can only admit.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::{HashMap, HashSet};

/// Deeper expressions than this are outside the model; each step is one bounded frame.
const DEPTH: usize = 96;
/// Refinement rounds before the model gives up; each adds a discriminant.
const ROUNDS: usize = 16;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Answer {
    Yes,
    No,
    Unknown,
}

/// How the pin's elaboration of a pattern ended, when it did not succeed.
enum Stop {
    /// The pin's `Type mismatch` or `Application type mismatch`: the types, rendered.
    Mismatch(String, String),
    /// Outside the model: the pin's answer is not known here.
    Unknown,
}

type Step<T> = Result<Result<T, Stop>, NatDefinitionElabError>;

/// A discriminant of the match being replayed.
#[derive(Clone)]
struct Discriminant {
    value: Expr,
    /// `inferType discr`, over the original locals: `getIndexToInclude?` walks this one.
    type_: Expr,
    /// Its binder type in the match type, earlier discriminants abstracted to placeholders
    /// (`elabMatchTypeAndDiscrs`'s `kabstract`).
    slot: Expr,
    placeholder: FVarId,
}

/// An index term after the pin's `whnfD`, as far as `findDiscrRefinementPath` reads it.
enum Shape {
    Var,
    /// A constructor application and its arguments (a positive Nat offset is `Nat.succ`).
    Constructor(Name, Vec<Expr>),
    /// A literal, an unassigned metavariable or a constant: no path goes through it.
    Atomic,
}

/// A path to an index (`findDiscrRefinementPath`), none, or outside the model.
enum Path {
    Found(Vec<usize>),
    None,
    Unknown,
}

struct Model<'c> {
    cx: &'c mut Context,
    assigned: HashMap<Name, Expr>,
    next: u64,
    /// Source names of pattern variables and placeholders, for messages.
    names: HashMap<FVarId, Name>,
    /// Arguments whose elaboration the pin postponed (application mode): synthetic placeholders
    /// that no unification assigns before the application meets its expected type.
    placeholders: HashSet<Name>,
    /// Application mode: an unassigned metavariable applied to arguments is the pin's stuck
    /// equation, which fails against a rigid term (measured, see `check_application_typing`).
    applications: bool,
}

impl Context {
    /// Refuse a match the pin refuses for its patterns' types (module docs). `discriminants`
    /// are the elaborated discriminants (value, type) in order, `alternatives` its
    /// `Term.matchAlt`s as written.
    pub(super) fn check_pattern_typing(
        &mut self,
        discriminants: &[(Expr, Expr)],
        alternatives: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let mut model = Model {
            cx: self,
            assigned: HashMap::new(),
            next: 0,
            names: HashMap::new(),
            placeholders: HashSet::new(),
            applications: false,
        };
        match model.run(discriminants, alternatives)? {
            Some((actual, expected)) => Err(failure(SourceInferenceError::TypeMismatch {
                actual,
                expected,
            })),
            None => Ok(()),
        }
    }
}

impl Context {
    /// R1 of franken_lean-z8j.1.6.3: refuse an application the pin refuses because it postponed
    /// one of its arguments. When an explicit argument's expected type is a metavariable applied
    /// to terms (`?P 7`, `?P n` for an implicit `{P : A → Type}` the expected type was not
    /// propagated to, since the result type depends on the explicit arguments) and the
    /// argument's own type is rigid (`Bool`), `ensureArgType` fails and the coercion is
    /// postponed: the argument becomes a synthetic placeholder (`Witness.intro 7 ?m.8`). The
    /// application then meets its expected type before that placeholder is resolved, so where
    /// the result type puts the placeholder against a rigid term (`… 7 true`) the pin reports a
    /// type mismatch. So does a result type that is itself such a stuck application against a
    /// rigid expected type (`g 3 true : ?P 3` against `(fun _ => Bool) 3`). Measured at the pin
    /// on 2026-10-10 (one file per program): refused with a literal or a local index, a local
    /// value, under an ascription; accepted when `P` is given (`@`, `(P := …)`), when the
    /// result does not depend on the explicit arguments (the expected type is propagated
    /// first), and when the result mentions only `P` itself (`Sigma P`).
    pub(super) fn check_application_typing(
        &mut self,
        syntax: &Syntax,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let mut model = Model {
            cx: self,
            assigned: HashMap::new(),
            next: 0,
            names: HashMap::new(),
            placeholders: HashSet::new(),
            applications: true,
        };
        match model.application_verdict(syntax, expected)? {
            Some((actual, expected)) => Err(failure(SourceInferenceError::TypeMismatch {
                actual,
                expected,
            })),
            None => Ok(()),
        }
    }
}

/// An explicit argument as the application model reads it.
enum Argument {
    Hole,
    Numeral(u64),
    /// A value of a known type (a Boolean constant, a local without a value).
    Typed(Expr, Expr),
    /// Anything else: elaborated by the pin in ways the model does not follow.
    Other,
}

/// Head-lambda applications reduced (`(fun x => b) a` to `b[a]`), as `whnfCore` does.
fn beta(expr: Expr, depth: usize) -> Result<Expr, NatDefinitionElabError> {
    let (head, args) = spine(&expr);
    if args.is_empty() || !matches!(head.node(), ExprNode::Lam { .. }) || depth > DEPTH {
        return Ok(expr);
    }
    let mut body = head.clone();
    let mut rest = args.into_iter().cloned().collect::<Vec<_>>().into_iter();
    let mut leftover = Vec::new();
    for arg in rest.by_ref() {
        match body.node() {
            ExprNode::Lam { body: inner, .. } => {
                body = inner
                    .subst_loose(0, std::slice::from_ref(&arg))
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
            }
            _ => {
                leftover.push(arg);
                break;
            }
        }
    }
    leftover.extend(rest);
    let reduced = leftover.into_iter().fold(body, Expr::app);
    beta(reduced, depth + 1)
}

fn nat() -> Name {
    Name::from_components(["Nat"])
}

fn nat_literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
}

fn spine(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut head = expr;
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

fn const_name(expr: &Expr) -> Option<&Name> {
    match expr.node() {
        ExprNode::Const { name, .. } => Some(name),
        _ => None,
    }
}

fn is_const(expr: &Expr, name: &[&str]) -> bool {
    const_name(expr) == Some(&Name::from_components(name.iter().copied()))
}

/// `e = base + offset` read as the pin's `isOffset?`/`evalNat` do: a literal or numeral, `Nat.zero`,
/// `Nat.succ e` and `e + k` for a closed `k` (`HAdd.hAdd`, `Add.add` or `Nat.add` at `Nat`). The
/// base is `None` for a closed term.
fn nat_view(expr: &Expr, depth: usize) -> Option<(Option<Expr>, u64)> {
    if depth > DEPTH {
        return None;
    }
    if let ExprNode::Lit {
        literal: Literal::Nat(value),
    } = expr.node()
    {
        return value.to_u64().map(|value| (None, value));
    }
    if is_const(expr, &["Nat", "zero"]) {
        return Some((None, 0));
    }
    let (head, args) = spine(expr);
    let shifted = |base: &Expr, by: u64| -> Option<(Option<Expr>, u64)> {
        match nat_view(base, depth + 1) {
            Some((base, offset)) => Some((base, offset.checked_add(by)?)),
            None => Some((Some(base.clone()), by)),
        }
    };
    let closed = |term: &Expr| match nat_view(term, depth + 1) {
        Some((None, value)) => Some(value),
        _ => None,
    };
    let nat_args = |args: &[&Expr]| args.iter().all(|arg| is_const(arg, &["Nat"]));
    if is_const(head, &["Nat", "succ"]) && args.len() == 1 {
        return shifted(args[0], 1);
    }
    if is_const(head, &["OfNat", "ofNat"]) && args.len() == 3 && nat_args(&args[..1]) {
        return closed(args[1]).map(|value| (None, value));
    }
    let (left, right) = if is_const(head, &["HAdd", "hAdd"]) && args.len() == 6 {
        if !nat_args(&args[..3]) {
            return None;
        }
        (args[4], args[5])
    } else if is_const(head, &["Add", "add"]) && args.len() == 4 && nat_args(&args[..1]) {
        (args[2], args[3])
    } else if is_const(head, &["Nat", "add"]) && args.len() == 2 {
        (args[0], args[1])
    } else {
        return None;
    };
    let by = closed(right)?;
    shifted(left, by)
}

/// An offset term proper: a closed term or a positive offset (`isDefEqOffsetNat` compares these).
fn offset_term(expr: &Expr) -> Option<(Option<Expr>, u64)> {
    nat_view(expr, 0).filter(|(base, offset)| base.is_none() || *offset > 0)
}

fn without_zero(expr: Expr) -> Expr {
    match nat_view(&expr, 0) {
        Some((Some(base), 0)) => base,
        _ => expr,
    }
}

fn with_offset(base: Option<Expr>, offset: u64) -> Expr {
    match base {
        None => nat_literal(offset),
        Some(base) if offset == 0 => base,
        Some(base) => Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["Nat", "add"]), vec![]),
                base,
            ),
            nat_literal(offset),
        ),
    }
}

impl Model<'_> {
    fn run(
        &mut self,
        discriminants: &[(Expr, Expr)],
        alternatives: &[Syntax],
    ) -> Result<Option<(String, String)>, NatDefinitionElabError> {
        // Each `|`-separated group of patterns is an alternative of its own (`expandMatchAlts?`).
        let mut rows = Vec::new();
        for alternative in alternatives {
            self.cx.tick()?;
            let Syntax::Node { kind, args, .. } = alternative else {
                return Ok(None);
            };
            if kind != &parser_kind(&["Term", "matchAlt"]) || args.len() != 4 {
                return Ok(None);
            }
            let Syntax::Node { args: groups, .. } = &args[1] else {
                return Ok(None);
            };
            for group in groups {
                if matches!(group, Syntax::Atom { val, .. } if val == "|") {
                    continue;
                }
                let Syntax::Node { args: elements, .. } = group else {
                    return Ok(None);
                };
                let row: Vec<&Syntax> = elements.iter().step_by(2).collect();
                if row.len() != discriminants.len() {
                    return Ok(None);
                }
                rows.push(row);
            }
        }
        let mut discrs = Vec::new();
        for (value, type_) in discriminants {
            self.cx.tick()?;
            let value = self.cx.instantiate(value)?;
            let type_ = self.cx.instantiate(type_)?;
            if value.has_expr_mvar() || type_.has_expr_mvar() || type_.has_loose_bvars() {
                return Ok(None);
            }
            // Earlier discriminants are abstracted in this one's type. A local's occurrences are
            // exact; anything else is matched up to definitional equality by `kabstract`, which
            // the model does not replay unless its head occurs nowhere.
            let mut slot = type_.clone();
            for earlier in &discrs {
                let Discriminant {
                    value: earlier_value,
                    placeholder,
                    ..
                } = earlier;
                slot = match earlier_value.node() {
                    ExprNode::FVar { id } => {
                        replace_fvar(&slot, id, &Expr::fvar(placeholder.clone()))?
                    }
                    _ if mentions_head(&slot, earlier_value) => return Ok(None),
                    _ => slot,
                };
            }
            let placeholder = self.fresh_id("d");
            discrs.push(Discriminant {
                value,
                type_,
                slot,
                placeholder,
            });
        }
        let mut prefix = 0;
        let mut first: Option<(String, String)> = None;
        for _ in 0..ROUNDS {
            self.cx.tick()?;
            match self.round(&discrs, prefix, &rows)? {
                Round::Accepted | Round::Unknown => return Ok(None),
                // An error thrown in `elabPatterns` (no path, or the retry failing) leaves the
                // loop as itself; only the loop's own stops rethrow the first one (`throwEx`).
                Round::Refused(mismatch) => return Ok(Some(mismatch)),
                Round::Refine {
                    pattern,
                    path,
                    mismatch,
                } => {
                    first.get_or_insert(mismatch.clone());
                    // The discriminant the failing pattern belongs to, by position.
                    let Some(owner) = discrs.get(pattern) else {
                        return Ok(None);
                    };
                    let index = match self.index_to_include(&owner.type_.clone(), &path)? {
                        Ok(Some(index)) => index,
                        Ok(None) => return Ok(Some(first.unwrap_or(mismatch))),
                        Err(Stop::Unknown) | Err(Stop::Mismatch(..)) => return Ok(None),
                    };
                    for discr in &discrs {
                        match self.def_eq(&discr.value, &index)? {
                            Answer::Yes => return Ok(Some(first.unwrap_or(mismatch))),
                            Answer::Unknown => return Ok(None),
                            Answer::No => {}
                        }
                    }
                    // `collectDeps` would add locals whose types depend on the index; they are
                    // outside the model.
                    if let ExprNode::FVar { id } = index.node()
                        && self.has_dependents(id, &discrs)?
                    {
                        return Ok(None);
                    }
                    // `updateMatchType`: abstract the index in every slot, then prepend it.
                    let placeholder = self.fresh_id("d");
                    let mut updated = Vec::new();
                    for discr in &discrs {
                        let slot = match index.node() {
                            ExprNode::FVar { id } => {
                                replace_fvar(&discr.slot, id, &Expr::fvar(placeholder.clone()))?
                            }
                            _ => match self.abstract_term(&discr.slot, &index, &placeholder, 0)? {
                                Some(slot) => slot,
                                None => return Ok(None),
                            },
                        };
                        updated.push(Discriminant {
                            slot,
                            ..discr.clone()
                        });
                    }
                    if let ExprNode::FVar { id } = index.node()
                        && let Some(name) =
                            self.cx.txn.lctx.find(id).map(|decl| decl.user_name.clone())
                    {
                        self.names.insert(placeholder.clone(), name);
                    }
                    let mut next = vec![Discriminant {
                        value: index.clone(),
                        // Only its hole pattern meets this slot, which assigns anything.
                        type_: Expr::sort(Level::zero()),
                        slot: Expr::sort(Level::zero()),
                        placeholder,
                    }];
                    next.extend(updated);
                    discrs = next;
                    prefix += 1;
                }
            }
        }
        Ok(None)
    }

    /// One pass of `elabMatchAltViews`'s loop over every alternative; the first `prefix`
    /// discriminants are refinement indices, whose patterns are holes.
    fn round(
        &mut self,
        discrs: &[Discriminant],
        prefix: usize,
        rows: &[Vec<&Syntax>],
    ) -> Result<Round, NatDefinitionElabError> {
        for row in rows {
            self.assigned.clear();
            let mut values: Vec<(FVarId, Expr)> = Vec::new();
            let mut variables = HashMap::new();
            for (position, discr) in discrs.iter().enumerate() {
                self.cx.tick()?;
                let mut expected = discr.slot.clone();
                for (placeholder, value) in &values {
                    expected = replace_fvar(&expected, placeholder, value)?;
                }
                let expected = self.inst(&expected, 0)?;
                let Some(expected) = expected else {
                    return Ok(Round::Unknown);
                };
                if position < prefix {
                    let hole = self.fresh_mvar();
                    values.push((discr.placeholder.clone(), hole));
                    continue;
                }
                let syntax = row[position - prefix];
                let saved = (self.assigned.clone(), variables.clone());
                match self.pattern(syntax, &expected, true, &mut variables, 0)? {
                    Ok((value, _)) => {
                        values.push((discr.placeholder.clone(), value));
                        continue;
                    }
                    Err(Stop::Unknown) => return Ok(Round::Unknown),
                    Err(Stop::Mismatch(actual, wanted)) => {
                        (self.assigned, variables) = saved;
                        let mismatch = (actual, wanted);
                        // Elaborate again against the type with its indices erased
                        // (`eraseIndices`), not requiring the type to match, and look for a path.
                        let Some(erased) = self.erase_indices(&expected, 0)? else {
                            return Ok(Round::Unknown);
                        };
                        let mut retry_variables = variables.clone();
                        let (_, type_) =
                            match self.pattern(syntax, &erased, false, &mut retry_variables, 0)? {
                                Ok(typed) => typed,
                                Err(Stop::Unknown) => return Ok(Round::Unknown),
                                Err(Stop::Mismatch(..)) => return Ok(Round::Refused(mismatch)),
                            };
                        let Some(type_) = self.inst(&type_, 0)? else {
                            return Ok(Round::Unknown);
                        };
                        return Ok(match self.type_path(&type_, &expected, 0)? {
                            Path::Found(path) => Round::Refine {
                                pattern: position,
                                path,
                                mismatch,
                            },
                            Path::None => Round::Refused(mismatch),
                            Path::Unknown => Round::Unknown,
                        });
                    }
                }
            }
        }
        Ok(Round::Accepted)
    }

    fn fresh_id(&mut self, kind: &str) -> FVarId {
        self.next += 1;
        FVarId(Name::num(
            Name::from_components(["_fln_pin_pattern", kind]),
            self.next,
        ))
    }

    fn fresh_mvar(&mut self) -> Expr {
        self.next += 1;
        Expr::mvar(MVarId(Name::num(
            Name::from_components(["_fln_pin_pattern", "m"]),
            self.next,
        )))
    }

    fn fresh_placeholder(&mut self) -> Expr {
        self.next += 1;
        let id = Name::num(Name::from_components(["_fln_pin_pattern", "o"]), self.next);
        self.placeholders.insert(id.clone());
        Expr::mvar(MVarId(id))
    }

    fn placeholder(&self, expr: &Expr) -> bool {
        matches!(expr.node(), ExprNode::MVar { id } if self.placeholders.contains(&id.0))
    }

    /// A term that no reduction or assignment turns into anything else: a literal, a rigid
    /// local, a constructor or type application, a Nat offset.
    fn rigid_term(&self, expr: &Expr) -> bool {
        if offset_term(expr).is_some() {
            return true;
        }
        match expr.node() {
            ExprNode::Lit { .. } => return true,
            ExprNode::FVar { id } => return self.rigid(id),
            _ => {}
        }
        let (head, _) = spine(expr);
        const_name(head).is_some_and(|name| self.rigid_head(name))
    }

    /// `stuck` is an unassigned metavariable applied to terms; against a rigid `other` the pin's
    /// unifier fails (application mode only).
    fn stuck_against(&self, stuck: &Expr, other: &Expr) -> Option<Answer> {
        let (head, args) = spine(stuck);
        if args.is_empty() || self.model_mvar(head).is_none() {
            return None;
        }
        Some(if self.rigid_term(other) {
            Answer::No
        } else {
            Answer::Unknown
        })
    }

    fn model_mvar(&self, expr: &Expr) -> Option<Name> {
        let ExprNode::MVar { id } = expr.node() else {
            return None;
        };
        (id.0.parent() == Name::from_components(["_fln_pin_pattern", "m"])
            && !self.assigned.contains_key(&id.0))
        .then(|| id.0.clone())
    }

    /// A pattern variable, a placeholder, or a local of the enclosing context with no value:
    /// none can be assigned or unfolded.
    fn rigid(&self, id: &FVarId) -> bool {
        id.0.parent().parent() == Name::from_components(["_fln_pin_pattern"])
            || self
                .cx
                .txn
                .lctx
                .find(id)
                .is_some_and(|decl| decl.value.is_none())
    }

    fn constructor(&self, name: &Name) -> Option<fln_env::constants::ConstructorVal> {
        match self.cx.txn.env.find(name) {
            Some(ConstantInfo::Ctor(constructor)) => Some(constructor.clone()),
            _ => None,
        }
    }

    fn inductive(&self, name: &Name) -> Option<fln_env::constants::InductiveVal> {
        match self.cx.txn.env.find(name) {
            Some(ConstantInfo::Induct(inductive)) => Some(inductive.clone()),
            _ => None,
        }
    }

    /// A constant that never unfolds and is injective: a constructor or an inductive type.
    fn rigid_head(&self, name: &Name) -> bool {
        self.constructor(name).is_some() || self.inductive(name).is_some()
    }

    /// The model's metavariables replaced by their assignments; `None` past the depth bound.
    fn inst(&mut self, expr: &Expr, depth: usize) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(None);
        }
        if !expr.has_expr_mvar() {
            return Ok(Some(expr.clone()));
        }
        Ok(Some(match expr.node() {
            ExprNode::MVar { id } => match self.assigned.get(&id.0).cloned() {
                Some(value) => return self.inst(&value, depth + 1),
                None => expr.clone(),
            },
            ExprNode::App { f, a } => {
                let (Some(f), Some(a)) = (self.inst(f, depth + 1)?, self.inst(a, depth + 1)?)
                else {
                    return Ok(None);
                };
                Expr::app(f, a)
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (Some(binder_type), Some(body)) = (
                    self.inst(binder_type, depth + 1)?,
                    self.inst(body, depth + 1)?,
                ) else {
                    return Ok(None);
                };
                Expr::lam(binder_name.clone(), binder_type, body, *binder_info)
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let (Some(binder_type), Some(body)) = (
                    self.inst(binder_type, depth + 1)?,
                    self.inst(body, depth + 1)?,
                ) else {
                    return Ok(None);
                };
                Expr::forall_e(binder_name.clone(), binder_type, body, *binder_info)
            }
            // A metavariable under a `let`, metadata or a projection is outside the model.
            _ => return Ok(None),
        }))
    }

    /// `isDefEq` with assignment of the model's metavariables; a `No` or `Unknown` keeps no
    /// assignment it made (`checkpointDefEq`).
    fn def_eq(&mut self, left: &Expr, right: &Expr) -> Result<Answer, NatDefinitionElabError> {
        let saved = self.assigned.clone();
        let answer = self.compare(left, right, 0)?;
        if answer != Answer::Yes {
            self.assigned = saved;
        }
        Ok(answer)
    }

    fn compare(
        &mut self,
        left: &Expr,
        right: &Expr,
        depth: usize,
    ) -> Result<Answer, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(Answer::Unknown);
        }
        let (Some(left), Some(right)) = (self.inst(left, 0)?, self.inst(right, 0)?) else {
            return Ok(Answer::Unknown);
        };
        // `e + 0` reduces to `e` (`Nat.add`'s zero case), the shape `whnfD` leaves under a
        // `Nat.succ` it peeled from `e + 1`; a head lambda's application reduces (`whnfCore`).
        let (left, right) = (without_zero(beta(left, 0)?), without_zero(beta(right, 0)?));
        if left == right {
            return Ok(Answer::Yes);
        }
        if let Some(id) = self.model_mvar(&left) {
            return Ok(self.assign(id, &right));
        }
        if let Some(id) = self.model_mvar(&right) {
            return Ok(self.assign(id, &left));
        }
        // A postponed argument's placeholder is assigned by nothing here, so it never meets a
        // rigid term.
        if self.placeholder(&left) || self.placeholder(&right) {
            let other = if self.placeholder(&left) {
                &right
            } else {
                &left
            };
            return Ok(if self.rigid_term(other) {
                Answer::No
            } else {
                Answer::Unknown
            });
        }
        if self.applications
            && let Some(answer) = self
                .stuck_against(&left, &right)
                .or_else(|| self.stuck_against(&right, &left))
        {
            return Ok(answer);
        }
        // `isDefEqOffsetNat`: two offset terms compare by their bases once the common offset
        // is cancelled; a smaller literal than the offset is never equal.
        if let (Some((left_base, left_offset)), Some((right_base, right_offset))) =
            (offset_term(&left), offset_term(&right))
        {
            return match (left_base, right_base) {
                (None, None) => Ok(if left_offset == right_offset {
                    Answer::Yes
                } else {
                    Answer::No
                }),
                (Some(base), None) => match right_offset.checked_sub(left_offset) {
                    Some(rest) => self.compare(&base, &nat_literal(rest), depth + 1),
                    None => Ok(Answer::No),
                },
                (None, Some(base)) => match left_offset.checked_sub(right_offset) {
                    Some(rest) => self.compare(&nat_literal(rest), &base, depth + 1),
                    None => Ok(Answer::No),
                },
                (Some(left_base), Some(right_base)) => {
                    let common = left_offset.min(right_offset);
                    self.compare(
                        &with_offset(Some(left_base), left_offset - common),
                        &with_offset(Some(right_base), right_offset - common),
                        depth + 1,
                    )
                }
            };
        }
        match (left.node(), right.node()) {
            (ExprNode::FVar { id: x }, ExprNode::FVar { id: y }) => {
                return Ok(if self.rigid(x) && self.rigid(y) {
                    Answer::No
                } else {
                    Answer::Unknown
                });
            }
            (ExprNode::FVar { id }, _) => return Ok(self.rigid_against(id, &right)),
            (_, ExprNode::FVar { id }) => return Ok(self.rigid_against(id, &left)),
            (
                ExprNode::Lit {
                    literal: Literal::Str(_),
                },
                ExprNode::Lit {
                    literal: Literal::Str(_),
                },
            ) => return Ok(Answer::No),
            _ => {}
        }
        let (left_head, left_args) = spine(&left);
        let (right_head, right_args) = spine(&right);
        let (Some(left_name), Some(right_name)) = (const_name(left_head), const_name(right_head))
        else {
            return Ok(Answer::Unknown);
        };
        if !self.rigid_head(left_name) || !self.rigid_head(right_name) {
            return Ok(Answer::Unknown);
        }
        // A Nat literal against a constructor of Nat went through the offset comparison.
        if left_name != right_name || left_args.len() != right_args.len() {
            return Ok(Answer::No);
        }
        let mut answer = Answer::Yes;
        for (left, right) in left_args.into_iter().zip(right_args) {
            match self.compare(left, right, depth + 1)? {
                Answer::Yes => {}
                Answer::No => return Ok(Answer::No),
                Answer::Unknown => answer = Answer::Unknown,
            }
        }
        Ok(answer)
    }

    /// A rigid local against a term: never equal to a literal, a positive offset or a
    /// constructor or type application, since none reduces to a local.
    fn rigid_against(&self, id: &FVarId, other: &Expr) -> Answer {
        if !self.rigid(id) {
            return Answer::Unknown;
        }
        if offset_term(other).is_some() {
            return Answer::No;
        }
        let (head, _) = spine(other);
        match const_name(head) {
            Some(name) if self.rigid_head(name) => Answer::No,
            _ => Answer::Unknown,
        }
    }

    fn assign(&mut self, id: Name, value: &Expr) -> Answer {
        if value.has_loose_bvars() || occurs(&id, value, 0) != Some(false) {
            return Answer::Unknown;
        }
        self.assigned.insert(id, value.clone());
        Answer::Yes
    }

    /// Elaborate one pattern against `expected`: its value and type. `ensure` is the pin's
    /// `elabTermEnsuringType` (a top-level pattern's first attempt); its retry against erased
    /// indices does not require the type to match.
    fn pattern(
        &mut self,
        syntax: &Syntax,
        expected: &Expr,
        ensure: bool,
        variables: &mut HashMap<Name, Expr>,
        depth: usize,
    ) -> Step<(Expr, Expr)> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(Err(Stop::Unknown));
        }
        if let Some(inner) = parenthesized_inner(syntax)? {
            return self.pattern(inner, expected, ensure, variables, depth + 1);
        }
        let hole = parser_kind(&["Term", "hole"]);
        let synthetic = parser_kind(&["Term", "syntheticHole"]);
        if matches!(syntax.kind(), Some(kind) if kind == &hole || kind == &synthetic) {
            return Ok(Ok((self.fresh_mvar(), expected.clone())));
        }
        if syntax.kind() == Some(&Name::from_components(["num"])) {
            // A numeral is `OfNat.ofNat ?α n ?inst`; only at `Nat` is its value known here.
            let Syntax::Node { args, .. } = syntax else {
                return Ok(Err(Stop::Unknown));
            };
            let [Syntax::Atom { val, .. }] = args.as_slice() else {
                return Ok(Err(Stop::Unknown));
            };
            let Some(expected) = self.inst(expected, 0)? else {
                return Ok(Err(Stop::Unknown));
            };
            if const_name(&expected) != Some(&nat()) {
                return Ok(Err(Stop::Unknown));
            }
            let Ok(Literal::Nat(value)) = decode_natural(val) else {
                return Ok(Err(Stop::Unknown));
            };
            return Ok(Ok((Expr::lit(Literal::Nat(value)), expected)));
        }
        let (head, arguments) = match syntax {
            Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Term", "app"]) => {
                let [
                    head,
                    Syntax::Node {
                        args: arguments, ..
                    },
                ] = args.as_slice()
                else {
                    return Ok(Err(Stop::Unknown));
                };
                (head, arguments.iter().collect::<Vec<_>>())
            }
            _ => (syntax, Vec::new()),
        };
        let constructor = match head {
            Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Term", "dotIdent"]) => {
                let [_, Syntax::Ident { val, .. }] = args.as_slice() else {
                    return Ok(Err(Stop::Unknown));
                };
                // `.c` names a constructor of the expected type's family.
                let Some(expected) = self.inst(expected, 0)? else {
                    return Ok(Err(Stop::Unknown));
                };
                let (family, _) = spine(&expected);
                match const_name(family).filter(|name| self.inductive(name).is_some()) {
                    Some(family) => family.clone().append_core(val),
                    None => return Ok(Err(Stop::Unknown)),
                }
            }
            Syntax::Ident { val, .. } => {
                let Ok(resolved) = self.cx.resolve_source_name(val) else {
                    return Ok(Err(Stop::Unknown));
                };
                let resolved = resolved.unwrap_or_else(|| val.clone());
                if self.constructor(&resolved).is_some() {
                    resolved
                } else if matches!(val.to_display_string().as_str(), "true" | "false") {
                    Name::from_components(["Bool"]).append_core(val)
                } else if arguments.is_empty() && !val.is_anonymous() && val.parent().is_anonymous()
                {
                    // A pattern variable: a local the pattern binds, never assigned.
                    if variables.contains_key(val) {
                        return Ok(Err(Stop::Unknown));
                    }
                    let id = self.fresh_id("v");
                    self.names.insert(id.clone(), val.clone());
                    let variable = Expr::fvar(id);
                    variables.insert(val.clone(), variable.clone());
                    return Ok(Ok((variable, expected.clone())));
                } else {
                    return Ok(Err(Stop::Unknown));
                }
            }
            _ => return Ok(Err(Stop::Unknown)),
        };
        self.application(&constructor, &arguments, expected, ensure, variables, depth)
    }

    /// A constructor applied to explicit argument patterns (`elabAppArgs` with the pin's order).
    fn application(
        &mut self,
        constructor: &Name,
        arguments: &[&Syntax],
        expected: &Expr,
        ensure: bool,
        variables: &mut HashMap<Name, Expr>,
        depth: usize,
    ) -> Step<(Expr, Expr)> {
        let Some(info) = self.constructor(constructor) else {
            return Ok(Err(Stop::Unknown));
        };
        let levels = info
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let mut value = Expr::const_(constructor.clone(), levels);
        let mut type_ = info.base.type_.clone();
        let mut remaining = arguments.iter();
        let mut propagated = false;
        let mut binder = 0u32;
        while let ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } = type_.node()
        {
            self.cx.tick()?;
            let (binder_type, body) = (binder_type.clone(), body.clone());
            let argument = if *binder_info == BinderInfo::Default {
                // An explicit parameter of the family (a promoted index) is an inaccessible
                // position, which FrankenLean's lowering refuses by name; leave it there.
                if binder < info.num_params {
                    return Ok(Err(Stop::Unknown));
                }
                let Some(syntax) = remaining.next() else {
                    return Ok(Err(Stop::Unknown));
                };
                if !propagated {
                    propagated = true;
                    // `propagateExpectedType`, before the first explicit argument unless it is a
                    // hole: only when the result depends on no remaining argument.
                    let hole = matches!(syntax.kind(), Some(kind)
                        if kind == &parser_kind(&["Term", "hole"])
                            || kind == &parser_kind(&["Term", "syntheticHole"]));
                    if !hole
                        && let Some(result) = result_type(&type_)
                        && self.def_eq(&result, expected)? == Answer::Unknown
                    {
                        return Ok(Err(Stop::Unknown));
                    }
                }
                let Some(binder_type) = self.inst(&binder_type, 0)? else {
                    return Ok(Err(Stop::Unknown));
                };
                match self.pattern(syntax, &binder_type, true, variables, depth + 1)? {
                    Ok((argument, _)) => argument,
                    // A nested pattern is never refined: its mismatch is the pin's
                    // `Application type mismatch`.
                    Err(stop) => return Ok(Err(stop)),
                }
            } else {
                self.fresh_mvar()
            };
            type_ = body
                .subst_loose(0, std::slice::from_ref(&argument))
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value = Expr::app(value, argument);
            binder += 1;
        }
        if remaining.next().is_some() {
            return Ok(Err(Stop::Unknown));
        }
        match self.def_eq(&type_, expected)? {
            Answer::Yes => Ok(Ok((value, type_))),
            // The retry's `elabTermAndSynthesize` does not require the type.
            Answer::No if !ensure => Ok(Ok((value, type_))),
            Answer::No => Ok(Err(Stop::Mismatch(
                self.render(&type_, 0)?,
                self.render(expected, 0)?,
            ))),
            Answer::Unknown => Ok(Err(Stop::Unknown)),
        }
    }

    /// The pin's `elabAppArgs` over an application written as `c a₁ … aₙ` against `expected`,
    /// as far as R1 needs it (`check_application_typing`). `None` where the pin's verdict is
    /// not decided here.
    fn application_verdict(
        &mut self,
        syntax: &Syntax,
        expected: &Expr,
    ) -> Result<Option<(String, String)>, NatDefinitionElabError> {
        let mut syntax = syntax;
        while let Some(inner) = parenthesized_inner(syntax)? {
            syntax = inner;
        }
        let Syntax::Node { kind, args, .. } = syntax else {
            return Ok(None);
        };
        if kind != &parser_kind(&["Term", "app"]) {
            return Ok(None);
        }
        let [
            Syntax::Ident { val, .. },
            Syntax::Node {
                args: arguments, ..
            },
        ] = args.as_slice()
        else {
            return Ok(None);
        };
        if self.cx.txn.lctx.find_by_user_name(val).is_some() {
            return Ok(None);
        }
        // An ambiguous or unknown head is the elaborator's to report, in the pin's words.
        let Ok(Some(name)) = self.cx.resolve_source_name(val) else {
            return Ok(None);
        };
        let Some(constant) = self.cx.txn.env.find(&name).cloned() else {
            return Ok(None);
        };
        let expected = self.cx.instantiate(expected)?;
        if expected.has_expr_mvar() || expected.has_loose_bvars() {
            return Ok(None);
        }
        let mut type_ = constant.constant_val().type_.clone();
        let mut remaining = arguments.iter();
        let mut propagated = false;
        let mut uncertain = false;
        // The metavariables implicit binders introduced: the measured stuck heads (`{P}`).
        let mut implicit = HashSet::new();
        while let ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } = type_.node()
        {
            self.cx.tick()?;
            let (binder_type, body) = (binder_type.clone(), body.clone());
            let value = if *binder_info == BinderInfo::Default {
                let Some(syntax) = remaining.next() else {
                    return Ok(None);
                };
                let argument = self.app_argument(syntax)?;
                if !propagated {
                    propagated = true;
                    if !matches!(argument, Argument::Hole)
                        && let Some(result) = result_type(&type_)
                        && self.def_eq(&result, &expected)? == Answer::Unknown
                    {
                        return Ok(None);
                    }
                }
                let Some(binder) = self.inst(&binder_type, 0)? else {
                    return Ok(None);
                };
                let binder = beta(binder, 0)?;
                let stuck = {
                    let (head, args) = spine(&binder);
                    !args.is_empty()
                        && self
                            .model_mvar(head)
                            .is_some_and(|name| implicit.contains(&name))
                };
                match argument {
                    Argument::Hole => self.fresh_mvar(),
                    Argument::Numeral(value) => {
                        if self.model_mvar(&binder).is_some() || const_name(&binder) == Some(&nat())
                        {
                            nat_literal(value)
                        } else {
                            return Ok(None);
                        }
                    }
                    Argument::Typed(value, argument_type) => {
                        if stuck {
                            // `ensureArgType` fails on the stuck equation and the coercion is
                            // postponed. An earlier argument the model did not follow could have
                            // assigned the head, so the placeholder is only certain before one.
                            if uncertain || !self.rigid_term(&argument_type) {
                                return Ok(None);
                            }
                            self.fresh_placeholder()
                        } else if self.def_eq(&argument_type, &binder)? == Answer::Yes {
                            value
                        } else {
                            return Ok(None);
                        }
                    }
                    Argument::Other => {
                        uncertain = true;
                        self.fresh_mvar()
                    }
                }
            } else {
                let hole = self.fresh_mvar();
                if let Some(name) = self.model_mvar(&hole) {
                    implicit.insert(name);
                }
                hole
            };
            type_ = body
                .subst_loose(0, std::slice::from_ref(&value))
                .map_err(|_| failure(SourceInferenceError::Scope))?;
        }
        if remaining.next().is_some() {
            return Ok(None);
        }
        // The application meets its expected type before any postponed argument is resolved.
        if self.pinned(&type_, &expected, 0)? {
            return Ok(Some((self.render(&type_, 0)?, self.render(&expected, 0)?)));
        }
        if !uncertain && self.def_eq(&type_, &expected)? == Answer::No {
            let (Some(result), Some(wanted)) = (self.inst(&type_, 0)?, self.inst(&expected, 0)?)
            else {
                return Ok(None);
            };
            let (result, wanted) = (beta(result, 0)?, beta(wanted, 0)?);
            // Only the measured stuck result is refused here (`?P 3` for an implicit `{P}` against
            // a rigid type); any other `No` is left alone. An argument that is a local makes the
            // equation a pattern the pin may solve (`False.rec _ h : ?motive h`).
            let (head, args) = spine(&result);
            let implicit_head = self
                .model_mvar(head)
                .is_some_and(|name| implicit.contains(&name));
            let pattern = args
                .iter()
                .any(|arg| matches!(arg.node(), ExprNode::FVar { .. }));
            if implicit_head && !pattern && self.stuck_against(&result, &wanted) == Some(Answer::No)
            {
                return Ok(Some((self.render(&result, 0)?, self.render(&wanted, 0)?)));
            }
        }
        Ok(None)
    }

    /// An explicit argument's syntax, read as far as R1 needs.
    fn app_argument(&mut self, syntax: &Syntax) -> Result<Argument, NatDefinitionElabError> {
        let mut syntax = syntax;
        while let Some(inner) = parenthesized_inner(syntax)? {
            syntax = inner;
        }
        let hole = parser_kind(&["Term", "hole"]);
        let synthetic = parser_kind(&["Term", "syntheticHole"]);
        if matches!(syntax.kind(), Some(kind) if kind == &hole || kind == &synthetic) {
            return Ok(Argument::Hole);
        }
        if syntax.kind() == Some(&Name::from_components(["num"])) {
            if let Syntax::Node { args, .. } = syntax
                && let [Syntax::Atom { val, .. }] = args.as_slice()
                && let Ok(Literal::Nat(value)) = decode_natural(val)
                && let Some(value) = value.to_u64()
            {
                return Ok(Argument::Numeral(value));
            }
            return Ok(Argument::Other);
        }
        // `(e : T)` with `T` a parameterless inductive type (`Nat`, `Bool`): its type is known
        // and rigid; its value is left to the elaborator.
        if syntax.kind() == Some(&parser_kind(&["Term", "typeAscription"])) {
            if let Syntax::Node { args, .. } = syntax
                && args.len() == 5
                && let Syntax::Node {
                    args: annotation, ..
                } = &args[3]
                && let [Syntax::Ident { val, .. }] = annotation.as_slice()
                && self.cx.txn.lctx.find_by_user_name(val).is_none()
                && let Ok(Some(name)) = self.cx.resolve_source_name(val)
                && let Some(info) = self.inductive(&name)
                && info.num_params == 0
                && info.num_indices == 0
                && info.base.level_params.is_empty()
            {
                let value = self.fresh_mvar();
                return Ok(Argument::Typed(value, Expr::const_(name, vec![])));
            }
            return Ok(Argument::Other);
        }
        let Syntax::Ident { val, .. } = syntax else {
            return Ok(Argument::Other);
        };
        if let Some(decl) = self.cx.txn.lctx.find_by_user_name(val).cloned() {
            let type_ = self.cx.instantiate(&decl.type_)?;
            if decl.value.is_some() || type_.has_expr_mvar() {
                return Ok(Argument::Other);
            }
            return Ok(Argument::Typed(Expr::fvar(decl.id), type_));
        }
        let display = val.to_display_string();
        if display == "true" || display == "false" {
            let bool_ = Name::from_components(["Bool"]);
            return Ok(Argument::Typed(
                Expr::const_(bool_.append_core(val), vec![]),
                Expr::const_(bool_, vec![]),
            ));
        }
        Ok(Argument::Other)
    }

    /// Whether the result type puts a postponed argument's placeholder against a rigid term of
    /// the expected type, walking both through the same rigid heads.
    fn pinned(
        &mut self,
        result: &Expr,
        expected: &Expr,
        depth: usize,
    ) -> Result<bool, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(false);
        }
        let (Some(result), Some(expected)) = (self.inst(result, 0)?, self.inst(expected, 0)?)
        else {
            return Ok(false);
        };
        let (result, expected) = (beta(result, 0)?, beta(expected, 0)?);
        if self.placeholder(&result) {
            return Ok(self.rigid_term(&expected));
        }
        let (result_head, result_args) = spine(&result);
        let (expected_head, expected_args) = spine(&expected);
        let (Some(name), Some(other)) = (const_name(result_head), const_name(expected_head)) else {
            return Ok(false);
        };
        if name != other || !self.rigid_head(name) || result_args.len() != expected_args.len() {
            return Ok(false);
        }
        let pairs: Vec<(Expr, Expr)> = result_args
            .into_iter()
            .cloned()
            .zip(expected_args.into_iter().cloned())
            .collect();
        for (left, right) in pairs {
            if self.pinned(&left, &right, depth + 1)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// `eraseIndices`: the family's indices replaced by fresh metavariables, its parameters
    /// erased in turn. A type that is not an inductive family application is kept.
    fn erase_indices(
        &mut self,
        type_: &Expr,
        depth: usize,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(None);
        }
        let (head, args) = spine(type_);
        let Some(info) = const_name(head).and_then(|name| self.inductive(name)) else {
            return Ok(Some(type_.clone()));
        };
        let params = info.num_params as usize;
        if args.len() != params + info.num_indices as usize {
            return Ok(None);
        }
        let mut erased = head.clone();
        for (position, arg) in args.into_iter().enumerate() {
            let arg = if position < params {
                match self.erase_indices(arg, depth + 1)? {
                    Some(arg) => arg,
                    None => return Ok(None),
                }
            } else {
                self.fresh_mvar()
            };
            erased = Expr::app(erased, arg);
        }
        Ok(Some(erased))
    }

    /// `findDiscrRefinementPath`'s `goType`: the pattern's type against the expected one.
    fn type_path(
        &mut self,
        pattern: &Expr,
        expected: &Expr,
        depth: usize,
    ) -> Result<Path, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(Path::Unknown);
        }
        let (Some(pattern), Some(expected)) = (self.inst(pattern, 0)?, self.inst(expected, 0)?)
        else {
            return Ok(Path::Unknown);
        };
        let (pattern_head, pattern_args) = spine(&pattern);
        let (expected_head, expected_args) = spine(&expected);
        let (Some(name), Some(other)) = (const_name(pattern_head), const_name(expected_head))
        else {
            return Ok(Path::Unknown);
        };
        let Some(info) = self.inductive(name) else {
            return Ok(Path::Unknown);
        };
        if expected_args.is_empty() || name != other || pattern_args.len() != expected_args.len() {
            return Ok(Path::None);
        }
        let params = info.num_params as usize;
        let pairs: Vec<(Expr, Expr)> = pattern_args
            .into_iter()
            .cloned()
            .zip(expected_args.into_iter().cloned())
            .collect();
        for (position, (left, right)) in pairs.into_iter().enumerate() {
            match self.def_eq(&left, &right)? {
                Answer::Yes => continue,
                Answer::Unknown => return Ok(Path::Unknown),
                Answer::No => {}
            }
            let rest = if position < params {
                self.type_path(&left, &right, depth + 1)?
            } else {
                self.index_path(&left, &right, depth + 1)?
            };
            return Ok(match rest {
                Path::Found(mut path) => {
                    path.insert(0, position);
                    Path::Found(path)
                }
                other => other,
            });
        }
        Ok(Path::None)
    }

    /// `findDiscrRefinementPath`'s `goIndex`, on the pin's `whnfD` shapes.
    fn index_path(
        &mut self,
        pattern: &Expr,
        expected: &Expr,
        depth: usize,
    ) -> Result<Path, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(Path::Unknown);
        }
        let (Some(left), Some(right)) = (self.shape(pattern)?, self.shape(expected)?) else {
            return Ok(Path::Unknown);
        };
        let (name, left_args, right_args) = match (left, right) {
            (Shape::Var, _) | (_, Shape::Var) => return Ok(Path::Found(Vec::new())),
            (Shape::Constructor(left, left_args), Shape::Constructor(right, right_args))
                if left == right
                    && left_args.len() == right_args.len()
                    && !right_args.is_empty() =>
            {
                (left, left_args, right_args)
            }
            _ => return Ok(Path::None),
        };
        let Some(info) = self.constructor(&name) else {
            return Ok(Path::None);
        };
        let params = info.num_params as usize;
        for (position, (left, right)) in left_args.iter().zip(&right_args).enumerate() {
            match self.def_eq(left, right)? {
                Answer::Yes => continue,
                Answer::Unknown => return Ok(Path::Unknown),
                Answer::No if position < params => return Ok(Path::None),
                Answer::No => {}
            }
            return Ok(match self.index_path(left, right, depth + 1)? {
                Path::Found(mut path) => {
                    path.insert(0, position);
                    Path::Found(path)
                }
                other => other,
            });
        }
        Ok(Path::None)
    }

    /// The pin's `whnfD` of an index term, as far as the refinement reads it: closed Nat
    /// arithmetic is a literal, `e + k` is `Nat.succ (e + (k - 1))`, `e + 0` is `e`. `None` where
    /// the model does not know (a definition to unfold, a let-bound local).
    fn shape(&mut self, expr: &Expr) -> Result<Option<Shape>, NatDefinitionElabError> {
        let Some(expr) = self.inst(expr, 0)? else {
            return Ok(None);
        };
        if self.model_mvar(&expr).is_some() {
            return Ok(Some(Shape::Atomic));
        }
        if let Some((base, offset)) = nat_view(&expr, 0) {
            return Ok(match base {
                None => Some(Shape::Atomic),
                Some(base) if offset == 0 => return self.shape(&base),
                Some(base) => {
                    // `Nat.succ e` is itself; `e + k` unfolds through `Nat.add` one step.
                    let (head, args) = spine(&expr);
                    let argument = if is_const(head, &["Nat", "succ"]) {
                        args[0].clone()
                    } else {
                        with_offset_add(base, offset - 1)
                    };
                    Some(Shape::Constructor(
                        Name::from_components(["Nat", "succ"]),
                        vec![argument],
                    ))
                }
            });
        }
        match expr.node() {
            ExprNode::FVar { id } => return Ok(self.rigid(id).then_some(Shape::Var)),
            ExprNode::Lit { .. } => return Ok(Some(Shape::Atomic)),
            _ => {}
        }
        let (head, args) = spine(&expr);
        Ok(match const_name(head) {
            Some(name) if self.constructor(name).is_some() => Some(if args.is_empty() {
                Shape::Atomic
            } else {
                Shape::Constructor(name.clone(), args.into_iter().cloned().collect())
            }),
            _ => None,
        })
    }

    /// `getIndexToInclude?`: the subterm at `path` of the discriminant's type, each step after
    /// `whnfD`. `Ok(None)` when the path leaves an application (the pin then keeps its error).
    fn index_to_include(
        &mut self,
        type_: &Expr,
        path: &[usize],
    ) -> Result<Result<Option<Expr>, Stop>, NatDefinitionElabError> {
        let mut current = type_.clone();
        for (step, position) in path.iter().enumerate() {
            self.cx.tick()?;
            let args: Vec<Expr> = if step == 0 {
                let (head, args) = spine(&current);
                if !const_name(head).is_some_and(|name| self.inductive(name).is_some()) {
                    return Ok(Err(Stop::Unknown));
                }
                args.into_iter().cloned().collect()
            } else {
                match self.shape(&current)? {
                    Some(Shape::Constructor(_, args)) => args,
                    Some(Shape::Var | Shape::Atomic) => return Ok(Ok(None)),
                    None => return Ok(Err(Stop::Unknown)),
                }
            };
            let Some(next) = args.get(*position) else {
                return Ok(Ok(None));
            };
            current = next.clone();
        }
        Ok(Ok(Some(current)))
    }

    /// Whether a local in the discriminants' types depends on `index` without being one of
    /// them (`collectDeps` would add it).
    fn has_dependents(
        &mut self,
        index: &FVarId,
        discrs: &[Discriminant],
    ) -> Result<bool, NatDefinitionElabError> {
        let mut seen = Vec::new();
        for discr in discrs {
            collect_fvars(&discr.type_, &mut seen, 0);
        }
        for id in seen {
            self.cx.tick()?;
            if &id == index
                || discrs
                    .iter()
                    .any(|discr| matches!(discr.value.node(), ExprNode::FVar { id: value } if value == &id))
            {
                continue;
            }
            if let Some(decl) = self.cx.txn.lctx.find(&id)
                && (decl.type_.has_fvar() && mentions_fvar(&decl.type_, index, 0)
                    || decl
                        .value
                        .as_ref()
                        .is_some_and(|value| mentions_fvar(value, index, 0)))
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// `kabstract` of a non-local index: subterms with its head and arity that are
    /// definitionally equal to it become the placeholder. `None` when an answer is unknown.
    fn abstract_term(
        &mut self,
        expr: &Expr,
        index: &Expr,
        placeholder: &FVarId,
        depth: usize,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > DEPTH {
            return Ok(None);
        }
        let (index_head, index_args) = spine(index);
        let (head, args) = spine(expr);
        if const_name(head).is_some()
            && const_name(head) == const_name(index_head)
            && args.len() == index_args.len()
        {
            match self.def_eq(expr, index)? {
                Answer::Yes => return Ok(Some(Expr::fvar(placeholder.clone()))),
                Answer::Unknown => return Ok(None),
                Answer::No => {}
            }
        }
        Ok(Some(match expr.node() {
            ExprNode::App { f, a } => {
                let (Some(f), Some(a)) = (
                    self.abstract_term(f, index, placeholder, depth + 1)?,
                    self.abstract_term(a, index, placeholder, depth + 1)?,
                ) else {
                    return Ok(None);
                };
                Expr::app(f, a)
            }
            ExprNode::FVar { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. }
            | ExprNode::Sort { .. } => expr.clone(),
            _ => return Ok(None),
        }))
    }

    /// The pin-style rendering of a type, for the message.
    fn render(&mut self, expr: &Expr, depth: usize) -> Result<String, NatDefinitionElabError> {
        self.cx.tick()?;
        if depth > 8 {
            return Ok("…".to_owned());
        }
        let Some(expr) = self.inst(expr, 0)? else {
            return Ok("…".to_owned());
        };
        if let Some((base, offset)) = nat_view(&expr, 0) {
            return Ok(match base {
                None => offset.to_string(),
                Some(base) if offset == 0 => self.render(&base, depth + 1)?,
                Some(base) => format!("{} + {offset}", self.render(&base, depth + 1)?),
            });
        }
        Ok(match expr.node() {
            ExprNode::FVar { id } => self
                .names
                .get(id)
                .cloned()
                .or_else(|| self.cx.txn.lctx.find(id).map(|decl| decl.user_name.clone()))
                .map_or_else(|| "_".to_owned(), |name| name.to_display_string()),
            ExprNode::MVar { .. } => "?_".to_owned(),
            ExprNode::Const { name, .. } => name.to_display_string(),
            ExprNode::App { .. } => {
                let (head, args) = spine(&expr);
                let mut text = self.render(head, depth + 1)?;
                for arg in args {
                    let arg_text = self.render(arg, depth + 1)?;
                    if arg_text.contains(' ') {
                        text.push_str(&format!(" ({arg_text})"));
                    } else {
                        text.push(' ');
                        text.push_str(&arg_text);
                    }
                }
                text
            }
            _ => "…".to_owned(),
        })
    }
}

enum Round {
    /// Every alternative elaborated.
    Accepted,
    /// The pin's error stands: the match is refused.
    Refused((String, String)),
    /// A top-level pattern's mismatch has a refinement path.
    Refine {
        pattern: usize,
        path: Vec<usize>,
        mismatch: (String, String),
    },
    Unknown,
}

/// `e + k` written as `Nat.add e k` (`e` itself when `k` is zero), the shape `whnfD` leaves.
fn with_offset_add(base: Expr, offset: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_components(["Nat", "add"]), vec![]),
            base,
        ),
        nat_literal(offset),
    )
}

/// The result type once every remaining binder is passed, if it depends on none of them.
fn result_type(type_: &Expr) -> Option<Expr> {
    let mut type_ = type_;
    while let ExprNode::ForallE { body, .. } = type_.node() {
        type_ = body;
    }
    // The type has been instantiated up to here, so a loose variable is a remaining binder.
    (!type_.has_loose_bvars()).then(|| type_.clone())
}

/// Whether the model metavariable `id` occurs in `expr`; `None` past the depth bound.
fn occurs(id: &Name, expr: &Expr, depth: usize) -> Option<bool> {
    if depth > DEPTH {
        return None;
    }
    if !expr.has_expr_mvar() {
        return Some(false);
    }
    match expr.node() {
        ExprNode::MVar { id: other } => Some(&other.0 == id),
        ExprNode::App { f, a } => Some(occurs(id, f, depth + 1)? || occurs(id, a, depth + 1)?),
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => Some(occurs(id, binder_type, depth + 1)? || occurs(id, body, depth + 1)?),
        _ => None,
    }
}

fn mentions_fvar(expr: &Expr, id: &FVarId, depth: usize) -> bool {
    if depth > DEPTH {
        return true;
    }
    if !expr.has_fvar() {
        return false;
    }
    match expr.node() {
        ExprNode::FVar { id: other } => other == id,
        ExprNode::App { f, a } => {
            mentions_fvar(f, id, depth + 1) || mentions_fvar(a, id, depth + 1)
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => mentions_fvar(binder_type, id, depth + 1) || mentions_fvar(body, id, depth + 1),
        ExprNode::LetE {
            type_, value, body, ..
        } => {
            mentions_fvar(type_, id, depth + 1)
                || mentions_fvar(value, id, depth + 1)
                || mentions_fvar(body, id, depth + 1)
        }
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
            mentions_fvar(expr, id, depth + 1)
        }
        _ => false,
    }
}

fn collect_fvars(expr: &Expr, seen: &mut Vec<FVarId>, depth: usize) {
    if depth > DEPTH || !expr.has_fvar() {
        return;
    }
    match expr.node() {
        ExprNode::FVar { id } => {
            if !seen.contains(id) {
                seen.push(id.clone());
            }
        }
        ExprNode::App { f, a } => {
            collect_fvars(f, seen, depth + 1);
            collect_fvars(a, seen, depth + 1);
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            collect_fvars(binder_type, seen, depth + 1);
            collect_fvars(body, seen, depth + 1);
        }
        _ => {}
    }
}

/// Whether `expr` holds a subterm with `term`'s head constant and arity (`kabstract`'s key).
fn mentions_head(expr: &Expr, term: &Expr) -> bool {
    let (head, args) = spine(term);
    let Some(name) = const_name(head) else {
        return true;
    };
    let arity = args.len();
    let mut pending = vec![expr];
    while let Some(next) = pending.pop() {
        let (inner_head, inner_args) = spine(next);
        if const_name(inner_head) == Some(name) && inner_args.len() == arity {
            return true;
        }
        match next.node() {
            ExprNode::App { f, a } => {
                pending.push(f);
                pending.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(binder_type);
                pending.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push(type_);
                pending.push(value);
                pending.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

fn replace_fvar(expr: &Expr, id: &FVarId, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
    expr.abstract_fvar(id, 0)
        .and_then(|abstracted| abstracted.subst_loose(0, std::slice::from_ref(value)))
        .map_err(|_| failure(SourceInferenceError::Scope))
}
