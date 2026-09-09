//! Bidirectional elaboration of the native source subset.
//!
//! Syntax drives one private elaboration transaction. Applications insert typed
//! implicit metavariables; argument and expected-result types generate ordinary
//! unification equations. Only fully instantiated candidates leave this module.
//! The caller still owns final kernel checking and declaration publication.

mod infer;
mod instance_command;
mod instances;
mod levels;
mod record;
mod tactics;

use super::*;
use crate::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_core::expr::{FVarId, MVarId};
use fln_core::level::{LMVarId, Level};
use fln_core::options::KVMap;

#[derive(Debug, Clone, PartialEq)]
pub enum SourceInferenceError {
    UnknownConstant(Name),
    ExpectedFunction,
    ExpectedType,
    Record(crate::records::RecordError),
    Tactic(tactics::TacticError),
    UnresolvedHoles { count: usize },
    UnresolvedUniverses,
    InstanceSynthesisRequired,
    InvalidInstanceBinder,
    InstanceRegistry(crate::instances::InstanceRegistryError),
    ResourceLimit,
    Scope,
    Universe(crate::universe::UniverseInstantiationError),
    Unification(Box<UnificationError>),
}

impl std::fmt::Display for SourceInferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownConstant(_) => {
                write!(f, "source reference does not name a known constant")
            }
            Self::ExpectedFunction => write!(f, "source application requires a function type"),
            Self::Tactic(error) => write!(f, "{error}"),
            Self::Record(error) => write!(f, "{error}"),
            Self::ExpectedType => write!(f, "source annotation requires a type"),
            Self::UnresolvedHoles { count } => write!(
                f,
                "source elaboration left {count} unresolved metavariables"
            ),
            Self::UnresolvedUniverses => write!(f, "source elaboration left unresolved universes"),
            Self::InstanceSynthesisRequired => write!(
                f,
                "native instance search could not resolve all instance arguments"
            ),
            Self::InvalidInstanceBinder => write!(
                f,
                "instance binder must end in a registered class with inferable parameters"
            ),
            Self::InstanceRegistry(error) => write!(f, "{error}"),
            Self::ResourceLimit => write!(f, "source elaboration work limit reached"),
            Self::Scope => write!(
                f,
                "source elaboration encountered an invalid expression scope"
            ),
            Self::Universe(error) => write!(f, "{error}"),
            Self::Unification(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for SourceInferenceError {}

#[derive(Clone)]
struct Typed {
    value: Expr,
    type_: Expr,
}

#[derive(Clone)]
struct Context {
    txn: ElabTxn,
    kernel: Budget,
    next: u64,
    equations: Vec<(Expr, Expr)>,
    instance_goals: Vec<MVarId>,
}

fn failure(reason: SourceInferenceError) -> NatDefinitionElabError {
    NatDefinitionElabError::Inference(reason)
}

impl Context {
    fn new(env: &Environment, kernel: Budget) -> Self {
        let mut txn = ElabTxn::new(env.clone(), KVMap::new(), 0);
        txn.budget.max_heartbeats = 1_000_000;
        Self {
            txn,
            kernel,
            next: 0,
            equations: Vec::new(),
            instance_goals: Vec::new(),
        }
    }

    fn tick(&mut self) -> Result<(), NatDefinitionElabError> {
        self.txn
            .budget
            .check_heartbeat()
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))
    }

    fn fresh_name(&mut self) -> Result<Name, NatDefinitionElabError> {
        self.tick()?;
        let id = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        Ok(Name::num(Name::from_components(["_fln_source"]), id))
    }

    fn level(&mut self) -> Result<Level, NatDefinitionElabError> {
        Ok(Level::mvar(LMVarId(self.fresh_name()?)))
    }

    fn hole(&mut self, type_: Expr) -> Result<Expr, NatDefinitionElabError> {
        let name = self.fresh_name()?;
        let id = MVarId(name.clone());
        self.txn.mvars.declare(
            id.clone(),
            name,
            type_,
            self.txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        Ok(Expr::mvar(id))
    }

    fn instantiate(&mut self, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        self.txn
            .instantiate_expr(value)
            .map_err(|error| failure(SourceInferenceError::Universe(error)))
    }

    fn substitute(&mut self, body: &Expr, argument: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        body.subst_loose(0, std::slice::from_ref(argument))
            .map_err(|_| failure(SourceInferenceError::Scope))
    }

    fn constant(&mut self, name: &Name) -> Result<Typed, NatDefinitionElabError> {
        let info = self
            .txn
            .env
            .find(name)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))?;
        let base = info.constant_val();
        let mut levels = Vec::new();
        for _ in &base.level_params {
            levels.push(self.level()?);
        }
        let type_ = self.instantiate_params(&base.type_, &base.level_params, &levels)?;
        Ok(Typed {
            value: Expr::const_(name.clone(), levels),
            type_,
        })
    }

    fn atom(
        &mut self,
        syntax: &Syntax,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &parser_kind(&["Term", "hole"]) {
                let [hole] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(hole, "_", "placeholder")?;
                let type_ = match expected {
                    Some(type_) => type_.clone(),
                    None => {
                        let level = self.level()?;
                        self.hole(Expr::sort(level))?
                    }
                };
                return Ok(Typed {
                    value: self.hole(type_.clone())?,
                    type_,
                });
            }
            let level = if kind == &parser_kind(&["Term", "type"]) {
                let [keyword, level] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(keyword, "Type", "type universe")?;
                expect_empty_null(level, "absent universe level")?;
                Some(Level::one())
            } else if kind == &parser_kind(&["Term", "prop"]) {
                let [keyword] = args.as_slice() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                expect_atom(keyword, "Prop", "proposition universe")?;
                Some(Level::zero())
            } else {
                None
            };
            if let Some(level) = level {
                let type_ = Expr::sort(
                    level
                        .clone()
                        .succ()
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                );
                return Ok(Typed {
                    value: Expr::sort(level),
                    type_,
                });
            }
        }
        if let Syntax::Ident { val: name, .. } = syntax {
            if name.is_anonymous() {
                return Err(NatDefinitionElabError::AnonymousReferenceName);
            }
            if let Some(local) = self
                .txn
                .lctx
                .decls()
                .iter()
                .rev()
                .find(|local| &local.user_name == name)
            {
                return Ok(Typed {
                    value: Expr::fvar(local.id.clone()),
                    type_: local.type_.clone(),
                });
            }
            let mut resolved = name.clone();
            if !self.txn.env.contains(name) {
                if name == &Name::from_components(["true"]) {
                    resolved = Name::from_components(["Bool", "true"]);
                }
                if name == &Name::from_components(["false"]) {
                    resolved = Name::from_components(["Bool", "false"]);
                }
            }
            return self.constant(&resolved);
        }
        let value = elaborate_atom(syntax, &[], true, Some(&self.txn.env))?;
        let type_ = match value.node() {
            ExprNode::Lit {
                literal: Literal::Nat(_),
            } => nat_const(),
            ExprNode::Lit {
                literal: Literal::Str(_),
            } => string_const(),
            _ => return Err(failure(SourceInferenceError::ExpectedType)),
        };
        Ok(Typed { value, type_ })
    }

    fn whnf(&mut self, expr: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.whnf_with_transparency(expr, UnificationTransparency::SafeDefinitions, true)
    }

    fn whnf_with_transparency(
        &mut self,
        expr: &Expr,
        transparency: UnificationTransparency,
        zeta_delta: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut head = self.instantiate(expr)?;
        let mut arguments = Vec::new();
        let mut projections: Vec<(Name, u64, Vec<Expr>)> = Vec::new();
        loop {
            loop {
                self.tick()?;
                match head.node() {
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        projections.push((
                            struct_name.clone(),
                            *idx,
                            std::mem::take(&mut arguments),
                        ));
                        head = expr.clone();
                    }
                    ExprNode::MData { expr, .. } => head = expr.clone(),
                    ExprNode::App { f, a } => {
                        arguments.push(a.clone());
                        head = f.clone();
                    }
                    ExprNode::LetE { body, value, .. } => head = self.substitute(body, value)?,
                    ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                        let value = arguments.pop().expect("guarded application");
                        head = self.substitute(body, &value)?;
                    }
                    ExprNode::FVar { id } if zeta_delta => {
                        let value = self.txn.lctx.find(id).and_then(|local| local.value.clone());
                        match value {
                            Some(value) => head = value,
                            None => break,
                        }
                    }
                    ExprNode::Const { name, levels } => {
                        let Some(fln_env::constants::ConstantInfo::Defn(definition)) =
                            self.txn.env.find(name).cloned()
                        else {
                            break;
                        };
                        if definition.safety != DefinitionSafety::Safe
                            || !match transparency {
                                UnificationTransparency::None => false,
                                UnificationTransparency::Abbreviations => {
                                    definition.hints == ReducibilityHints::Abbrev
                                }
                                UnificationTransparency::SafeDefinitions => true,
                            }
                        {
                            break;
                        }
                        if definition.base.level_params.len() != levels.len() {
                            return Err(failure(SourceInferenceError::Scope));
                        }
                        head = self.instantiate_params(
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?;
                    }
                    _ => break,
                }
            }
            if let Some((structure, index, outer)) = projections.pop() {
                self.tick()?;
                if let Some(field) = crate::records::constructor_field(
                    &self.txn.env,
                    &structure,
                    index,
                    &head,
                    &arguments,
                ) {
                    head = field;
                    arguments = outer;
                    continue;
                }
                for argument in arguments.into_iter().rev() {
                    self.tick()?;
                    head = Expr::app(head, argument);
                }
                head = Expr::proj(structure, index, head);
                arguments = outer;
                // A stuck major cannot unlock an outer projection. Unwind without
                // feeding that same blocked projection back into the reduction loop.
                while let Some((structure, index, outer)) = projections.pop() {
                    self.tick()?;
                    for argument in arguments.into_iter().rev() {
                        self.tick()?;
                        head = Expr::app(head, argument);
                    }
                    head = Expr::proj(structure, index, head);
                    arguments = outer;
                }
            }
            for argument in arguments.into_iter().rev() {
                self.tick()?;
                head = Expr::app(head, argument);
            }
            return Ok(head);
        }
    }

    /// Enough type reconstruction to generate the universe side of an implicit
    /// type assignment. This is a constraint producer, not a trusted checker.
    fn leaf_type(&mut self, expression: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        let expression = self.instantiate(expression)?;
        match expression.node() {
            ExprNode::Sort { level } => Ok(Some(Expr::sort(
                level
                    .clone()
                    .succ()
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
            ))),
            ExprNode::MVar { id } => Ok(self.txn.mvars.get_decl(id).map(|decl| decl.type_.clone())),
            ExprNode::FVar { id } => Ok(self.txn.lctx.find(id).map(|local| local.type_.clone())),
            ExprNode::Const { name, levels } => {
                let Some(info) = self.txn.env.find(name).cloned() else {
                    return Ok(None);
                };
                let base = info.constant_val();
                Ok(Some(self.instantiate_params(
                    &base.type_,
                    &base.level_params,
                    levels,
                )?))
            }
            ExprNode::Lit {
                literal: Literal::Nat(_),
            } => Ok(Some(nat_const())),
            ExprNode::Lit {
                literal: Literal::Str(_),
            } => Ok(Some(string_const())),
            _ => Ok(None),
        }
    }

    fn constrain(&mut self, actual: &Expr, expected: &Expr) -> Result<(), NatDefinitionElabError> {
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        if !actual.has_expr_mvar()
            && !expected.has_expr_mvar()
            && !actual.has_level_mvar()
            && !expected.has_level_mvar()
        {
            // Closed constraints are checked by the declaration's ordinary K1
            // admission. Keeping them there preserves its original verdict.
            return Ok(());
        }
        if let (Some(left), Some(right)) = (self.known_type(&actual)?, self.known_type(&expected)?)
            && (left.has_level_mvar() || right.has_level_mvar())
        {
            self.equations.push((left, right));
        }
        self.equations.push((actual, expected));
        self.flush(false)
    }

    fn flush(&mut self, final_pass: bool) -> Result<(), NatDefinitionElabError> {
        if self.equations.is_empty() {
            return Ok(());
        }
        self.tick()?;
        match self.txn.unify_many_with(
            &self.equations,
            UnificationBudget::new(self.kernel),
            &|| false,
        ) {
            Ok(report) => {
                assert!(
                    report.awakened.is_empty(),
                    "this private source transaction has no queued consumer work"
                );
                self.equations.clear();
                Ok(())
            }
            Err(UnificationError::Deferred(_)) if !final_pass => Ok(()),
            Err(error) => Err(failure(SourceInferenceError::Unification(Box::new(error)))),
        }
    }

    fn insert_implicits(
        &mut self,
        mut term: Typed,
        explicit_follows: bool,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        loop {
            self.tick()?;
            term.type_ = self.whnf(&term.type_)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = term.type_.node()
            else {
                break;
            };
            let insert = match binder_info {
                BinderInfo::Default => false,
                BinderInfo::Implicit => explicit_follows || expected.is_some(),
                BinderInfo::StrictImplicit => explicit_follows,
                BinderInfo::InstImplicit => explicit_follows || expected.is_some(),
            };
            if !insert {
                break;
            }
            if !explicit_follows && let Some(expected) = expected {
                let expected = self.whnf(expected)?;
                if matches!(expected.node(), ExprNode::ForallE { binder_info: style, .. } if style == binder_info)
                {
                    break;
                }
            }
            let body = body.clone();
            let argument = if *binder_info == BinderInfo::InstImplicit {
                self.instance_hole(binder_type.clone())?
            } else {
                self.hole(binder_type.clone())?
            };
            term.value = Expr::app(term.value, argument.clone());
            term.type_ = self.substitute(&body, &argument)?;
        }
        Ok(term)
    }

    fn finish_term(
        &mut self,
        term: Typed,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let term = self.insert_implicits(term, false, expected)?;
        if let Some(expected) = expected {
            self.constrain(&term.type_, expected)?;
        }
        self.resolve_instances(false)?;
        Ok(term)
    }

    fn term(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Syntax, Option<Expr>, bool),
            Function(&'a [Syntax], Option<Expr>),
            Argument(Typed, Expr, &'a [Syntax], Option<Expr>),
            Apply(Typed, &'a [Syntax], Option<Expr>),
            Infix(BoundedInfixIntrinsic, Option<Expr>),
            Arrow(Option<Expr>),
            LetAnnotation(Name, &'a Syntax, &'a Syntax, Option<Expr>),
            LetValue(Name, Option<Expr>, &'a Syntax, Option<Expr>),
            LetBody(LocalContext, FVarId, Name, Typed),
            Lambda(LocalContext, Vec<LocalDecl>),
            RewriteTerm(
                tactics::ProofState<'a>,
                tactics::ProofGoal,
                bool,
                std::collections::VecDeque<tactics::RewriteRule<'a>>,
                bool,
            ),
            Proof(tactics::ProofState<'a>),
            ProofTerm(tactics::ProofState<'a>, tactics::ProofGoal, bool),
        }
        let mut tasks = vec![Task::Visit(syntax, expected, true)];
        let mut values: Vec<Typed> = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(syntax, expected, finish) => {
                    if let Some(inner) = parenthesized_inner(syntax)? {
                        tasks.push(Task::Visit(inner, expected, finish));
                        continue;
                    }
                    if let Syntax::Node { kind, args, .. } = syntax {
                        if kind == &parser_kind(&["Term", "byTactic"]) {
                            tasks.push(Task::Proof(self.start_proof(syntax, expected)?));
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "fun"]) {
                            let parts = expect_node(syntax, kind, 2, "Lean.Parser.Term.fun")?;
                            if !matches!(&parts[0], Syntax::Atom { val, .. } if val == "fun" || val == "λ")
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            let basic = expect_node(
                                &parts[1],
                                &parser_kind(&["Term", "basicFun"]),
                                4,
                                "Lean.Parser.Term.basicFun",
                            )?;
                            let names = expect_null_args(&basic[0], "lambda binders")?;
                            if names.is_empty() {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            expect_empty_null(&basic[1], "absent lambda result ascription")?;
                            if !matches!(&basic[2], Syntax::Atom { val, .. } if val == "=>" || val == "↦")
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            let saved = self.txn.lctx.clone();
                            let mut binders = Vec::new();
                            let mut expected_body = expected;
                            for name in names {
                                self.tick()?;
                                let Syntax::Ident { val: name, .. } = name else {
                                    return Err(failure(SourceInferenceError::Scope));
                                };
                                if name.is_anonymous() {
                                    return Err(NatDefinitionElabError::AnonymousReferenceName);
                                }
                                let (domain, codomain) = if let Some(expected) = &expected_body {
                                    let expected = self.whnf(expected)?;
                                    let ExprNode::ForallE {
                                        binder_type,
                                        body,
                                        binder_info: BinderInfo::Default,
                                        ..
                                    } = expected.node()
                                    else {
                                        return Err(failure(
                                            SourceInferenceError::ExpectedFunction,
                                        ));
                                    };
                                    (binder_type.clone(), Some(body.clone()))
                                } else {
                                    let universe = self.level()?;
                                    (self.hole(Expr::sort(universe))?, None)
                                };
                                let id = FVarId(self.fresh_name()?);
                                expected_body = codomain
                                    .map(|body| self.substitute(&body, &Expr::fvar(id.clone())))
                                    .transpose()?;
                                self.txn.lctx.add_param(
                                    id.clone(),
                                    name.clone(),
                                    domain,
                                    BinderInfo::Default,
                                );
                                binders.push(
                                    self.txn.lctx.find(&id).expect("new lambda binder").clone(),
                                );
                            }
                            tasks.push(Task::Lambda(saved, binders));
                            tasks.push(Task::Visit(&basic[3], expected_body, true));
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "let"]) {
                            let (name, annotation, value, body) = self.let_parts(args)?;
                            if let Some(annotation) = annotation {
                                tasks.push(Task::LetAnnotation(name, value, body, expected));
                                tasks.push(Task::Visit(annotation, None, true));
                            } else {
                                tasks.push(Task::LetValue(name, None, body, expected));
                                tasks.push(Task::Visit(value, None, true));
                            }
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "arrow"]) {
                            let [domain, arrow, codomain] = args.as_slice() else {
                                return Err(failure(SourceInferenceError::Scope));
                            };
                            if !matches!(arrow, Syntax::Atom { val, .. } if val == "->" || val == "→")
                            {
                                return Err(failure(SourceInferenceError::Scope));
                            }
                            tasks.push(Task::Arrow(expected));
                            tasks.push(Task::Visit(codomain, None, true));
                            tasks.push(Task::Visit(domain, None, true));
                            continue;
                        }
                        if kind == &parser_kind(&["Term", "app"]) {
                            let parts = expect_node(syntax, kind, 2, "application")?;
                            let arguments = expect_null_args(&parts[1], "application arguments")?;
                            if arguments.is_empty() {
                                return Err(failure(SourceInferenceError::ExpectedFunction));
                            }
                            tasks.push(Task::Function(arguments, expected));
                            tasks.push(Task::Visit(&parts[0], None, false));
                            continue;
                        }
                        if let Some(intrinsic) = bounded_infix_intrinsic(kind, true) {
                            let parts = expect_node(syntax, kind, 3, "scalar infix")?;
                            expect_atom(&parts[1], intrinsic.spelling(), "scalar operator")?;
                            tasks.push(Task::Infix(intrinsic, expected));
                            tasks.push(Task::Visit(&parts[2], None, true));
                            tasks.push(Task::Visit(&parts[0], None, true));
                            continue;
                        }
                    }
                    let term = self.atom(syntax, expected.as_ref())?;
                    values.push(if finish {
                        self.finish_term(term, expected.as_ref())?
                    } else {
                        term
                    });
                }
                Task::Proof(mut proof) => match self.advance_proof(&mut proof)? {
                    tactics::ProofAction::Rewrite {
                        goal,
                        rule,
                        remaining,
                        close,
                    } => {
                        self.txn.lctx = goal.lctx.clone();
                        tasks.push(Task::RewriteTerm(
                            proof,
                            goal,
                            rule.reverse,
                            remaining,
                            close,
                        ));
                        tasks.push(Task::Visit(rule.syntax, None, true));
                    }
                    tactics::ProofAction::Term {
                        syntax,
                        goal,
                        apply,
                    } => {
                        let expected = if apply {
                            None
                        } else {
                            Some(goal.target.clone())
                        };
                        self.txn.lctx = goal.lctx.clone();
                        tasks.push(Task::ProofTerm(proof, goal, apply));
                        tasks.push(Task::Visit(syntax, expected, true));
                    }
                    tactics::ProofAction::Complete(term) => values.push(term),
                },
                Task::RewriteTerm(mut proof, goal, reverse, remaining, close) => {
                    let term = values.pop().expect("rewrite rule visit");
                    self.rewrite_proof_term(&mut proof, goal, term, reverse, remaining, close)?;
                    tasks.push(Task::Proof(proof));
                }
                Task::ProofTerm(mut proof, goal, apply) => {
                    let term = values.pop().expect("tactic term visit");
                    if apply {
                        self.apply_proof_term(&mut proof, goal, term)?;
                    } else {
                        self.close_proof_goal(goal, term.value)?;
                    }
                    tasks.push(Task::Proof(proof));
                }
                Task::Lambda(saved, binders) => {
                    let mut body = values.pop().expect("lambda body visit");
                    self.flush(false)?;
                    body.value = self.instantiate(&body.value)?;
                    body.type_ = self.instantiate(&body.type_)?;
                    for local in binders.into_iter().rev() {
                        self.tick()?;
                        let domain = self.instantiate(&local.type_)?;
                        body.value = body
                            .value
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        body.type_ = body
                            .type_
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        body.value = Expr::lam(
                            local.user_name.clone(),
                            domain.clone(),
                            body.value,
                            local.binder_info,
                        );
                        body.type_ =
                            Expr::forall_e(local.user_name, domain, body.type_, local.binder_info);
                    }
                    self.txn.lctx = saved;
                    values.push(body);
                }
                Task::Function(arguments, expected) => {
                    let function = values.pop().expect("function task follows its visit");
                    tasks.push(Task::Apply(function, arguments, expected));
                }
                Task::Apply(function, arguments, expected) => {
                    if let Some((first, rest)) = arguments.split_first() {
                        let function = self.insert_implicits(function, true, None)?;
                        let ExprNode::ForallE {
                            binder_type, body, ..
                        } = function.type_.node()
                        else {
                            return Err(failure(SourceInferenceError::ExpectedFunction));
                        };
                        let domain = binder_type.clone();
                        let codomain = body.clone();
                        // Propagate a known result before checking the last
                        // explicit argument when the codomain does not depend
                        // on that argument (e.g. Inhabited.mk (fun x => ...)).
                        if rest.is_empty()
                            && !codomain.has_loose_bvar(0)
                            && let Some(expected) = &expected
                        {
                            self.constrain(&codomain, expected)?;
                        }
                        tasks.push(Task::Argument(function, codomain, rest, expected));
                        tasks.push(Task::Visit(first, Some(domain), true));
                    } else {
                        values.push(self.finish_term(function, expected.as_ref())?);
                    }
                }
                Task::Argument(function, codomain, rest, expected) => {
                    let argument = values.pop().expect("argument task follows its visit");
                    let type_ = self.substitute(&codomain, &argument.value)?;
                    tasks.push(Task::Apply(
                        Typed {
                            value: Expr::app(function.value, argument.value),
                            type_,
                        },
                        rest,
                        expected,
                    ));
                }
                Task::Infix(intrinsic, expected) => {
                    let right = values.pop().expect("infix right visit");
                    let left = values.pop().expect("infix left visit");
                    self.flush(false)?;
                    let name = match intrinsic {
                        BoundedInfixIntrinsic::Fixed { intrinsic, .. } => intrinsic,
                        BoundedInfixIntrinsic::ScalarBeq => {
                            if self.instantiate(&left.type_)? == string_const()
                                && self.instantiate(&right.type_)? == string_const()
                            {
                                Name::from_components(["String", "decEq"])
                            } else {
                                Name::from_components(["Nat", "beq"])
                            }
                        }
                    };
                    let mut function = self.constant(&name)?;
                    for argument in [left, right] {
                        function = self.insert_implicits(function, true, None)?;
                        let ExprNode::ForallE {
                            binder_type, body, ..
                        } = function.type_.node()
                        else {
                            return Err(failure(SourceInferenceError::ExpectedFunction));
                        };
                        let domain = binder_type.clone();
                        let body = body.clone();
                        let argument = self.finish_term(argument, Some(&domain))?;
                        self.constrain(&argument.type_, &domain)?;
                        function.type_ = self.substitute(&body, &argument.value)?;
                        function.value = Expr::app(function.value, argument.value);
                    }
                    values.push(self.finish_term(function, expected.as_ref())?);
                }
                Task::Arrow(expected) => {
                    let right = values.pop().expect("arrow codomain visit");
                    let left = values.pop().expect("arrow domain visit");
                    let u = self.sort_level(&left)?;
                    let v = self.sort_level(&right)?;
                    let level =
                        Level::imax(u, v).map_err(|_| failure(SourceInferenceError::Scope))?;
                    let body = right
                        .value
                        .lift_loose(0, 1)
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    let term = Typed {
                        value: Expr::forall_e(
                            Name::anonymous(),
                            left.value,
                            body,
                            BinderInfo::Default,
                        ),
                        type_: Expr::sort(level),
                    };
                    values.push(self.finish_term(term, expected.as_ref())?);
                }
                Task::LetAnnotation(name, value, body, expected) => {
                    let annotation = values.pop().expect("let annotation visit");
                    self.sort_level(&annotation)?;
                    tasks.push(Task::LetValue(
                        name,
                        Some(annotation.value.clone()),
                        body,
                        expected,
                    ));
                    tasks.push(Task::Visit(value, Some(annotation.value), true));
                }
                Task::LetValue(name, annotation, body, expected) => {
                    let mut value = values.pop().expect("let value visit");
                    if let Some(annotation) = annotation {
                        value.type_ = annotation;
                    }
                    let saved = self.txn.lctx.clone();
                    let id = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_let(
                        id.clone(),
                        name.clone(),
                        value.type_.clone(),
                        value.value.clone(),
                    );
                    tasks.push(Task::LetBody(saved, id, name, value));
                    tasks.push(Task::Visit(body, expected, true));
                }
                Task::LetBody(saved, id, name, value) => {
                    let mut body = values.pop().expect("let body visit");
                    body.value = self.instantiate(&body.value)?;
                    body.type_ = self.instantiate(&body.type_)?;
                    let abstract_body = body
                        .value
                        .abstract_fvar(&id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    let abstract_type = body
                        .type_
                        .abstract_fvar(&id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?;
                    let type_ = self.substitute(&abstract_type, &value.value)?;
                    values.push(Typed {
                        value: Expr::let_e(name, value.type_, value.value, abstract_body, false),
                        type_,
                    });
                    self.txn.lctx = saved;
                }
            }
        }
        let [result] = values.as_slice() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        Ok(result.clone())
    }

    fn let_parts<'a>(
        &mut self,
        parts: &'a [Syntax],
    ) -> Result<(Name, Option<&'a Syntax>, &'a Syntax, &'a Syntax), NatDefinitionElabError> {
        let [keyword, config, declaration, separator, body] = parts else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(keyword, "let", "let keyword")?;
        let config = expect_node(
            config,
            &parser_kind(&["Term", "letConfig"]),
            1,
            "let config",
        )?;
        expect_empty_null(&config[0], "empty let config")?;
        let wrapper = expect_node(
            declaration,
            &parser_kind(&["Term", "letDecl"]),
            1,
            "let declaration",
        )?;
        let declaration = expect_node(
            &wrapper[0],
            &parser_kind(&["Term", "letIdDecl"]),
            5,
            "let binding",
        )?;
        let id = expect_node(
            &declaration[0],
            &parser_kind(&["Term", "letId"]),
            1,
            "let identifier",
        )?;
        let Syntax::Ident { val: name, .. } = &id[0] else {
            return Err(failure(SourceInferenceError::Scope));
        };
        if name.is_anonymous() {
            return Err(NatDefinitionElabError::AnonymousReferenceName);
        }
        expect_empty_null(&declaration[1], "empty let parameters")?;
        let annotation = optional_type_syntax(&declaration[2])?;
        expect_atom(&declaration[3], ":=", "let assignment")?;
        expect_atom(separator, ";", "let separator")?;
        Ok((name.clone(), annotation, &declaration[4], body))
    }

    fn sort_level(&mut self, term: &Typed) -> Result<Level, NatDefinitionElabError> {
        let type_ = self.whnf(&term.type_)?;
        let ExprNode::Sort { level } = type_.node() else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        Ok(level.clone())
    }

    fn type_term(&mut self, syntax: &Syntax) -> Result<Expr, NatDefinitionElabError> {
        let term = self.term(syntax, None)?;
        self.sort_level(&term)?;
        Ok(term.value)
    }

    fn finish(&mut self, term: Typed) -> Result<Typed, NatDefinitionElabError> {
        self.resolve_instances(true)?;
        self.flush(true)?;
        let value = self.instantiate(&term.value)?;
        let type_ = self.instantiate(&term.type_)?;
        let mut holes = self.txn.mvars.collect_mvars(&value);
        holes.extend(self.txn.mvars.collect_mvars(&type_));
        if !holes.is_empty() {
            return Err(failure(SourceInferenceError::UnresolvedHoles {
                count: holes.len(),
            }));
        }
        if value.has_level_mvar() || type_.has_level_mvar() {
            return Err(failure(SourceInferenceError::UnresolvedUniverses));
        }
        Ok(Typed { value, type_ })
    }
}

fn optional_type_syntax(syntax: &Syntax) -> Result<Option<&Syntax>, NatDefinitionElabError> {
    let parts = expect_null_args(syntax, "optional type")?;
    if parts.is_empty() {
        return Ok(None);
    }
    let [annotation] = parts else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let parts = expect_node(
        annotation,
        &parser_kind(&["Term", "typeSpec"]),
        2,
        "type ascription",
    )?;
    expect_atom(&parts[0], ":", "type ascription colon")?;
    Ok(Some(&parts[1]))
}

impl Context {
    fn bind_parameters(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
        let mut parameters = Vec::new();
        for syntax in expect_null_args(syntax, "declaration binders")? {
            let Syntax::Node { kind, .. } = syntax else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if kind == &parser_kind(&["Term", "instBinder"]) {
                let parts = expect_node(syntax, kind, 4, "instance binder")?;
                expect_atom(&parts[0], "[", "instance binder opener")?;
                expect_atom(&parts[3], "]", "instance binder closer")?;
                let optional = expect_null_args(&parts[1], "optional instance name")?;
                let user_name = match optional {
                    [] => self.fresh_name()?,
                    [Syntax::Ident { val, .. }, colon] => {
                        expect_atom(colon, ":", "instance name colon")?;
                        val.clone()
                    }
                    _ => return Err(failure(SourceInferenceError::Scope)),
                };
                let domain = self.type_term(&parts[2])?;
                self.validate_instance_binder(&domain)?;
                let id = FVarId(self.fresh_name()?);
                self.txn.lctx.add_param(
                    id.clone(),
                    user_name.clone(),
                    domain.clone(),
                    BinderInfo::InstImplicit,
                );
                parameters.push(self.txn.lctx.find(&id).expect("inserted parameter").clone());
                continue;
            }
            let (style, open, close, arity) = if kind == &parser_kind(&["Term", "implicitBinder"]) {
                (BinderInfo::Implicit, "{", "}", 4)
            } else if kind == &parser_kind(&["Term", "strictImplicitBinder"]) {
                (BinderInfo::StrictImplicit, "⦃", "⦄", 4)
            } else if kind == &parser_kind(&["Term", "explicitBinder"]) {
                (BinderInfo::Default, "(", ")", 5)
            } else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let parts = expect_node(syntax, kind, arity, "typed binder")?;
            expect_atom(&parts[0], open, "binder opener")?;
            expect_atom(&parts[arity - 1], close, "binder closer")?;
            if style == BinderInfo::Default {
                expect_empty_null(&parts[3], "absent binder default")?;
            }
            let names = expect_null_args(&parts[1], "binder names")?;
            if names.is_empty() {
                return Err(failure(SourceInferenceError::Scope));
            }
            let type_parts = expect_null_args(&parts[2], "binder type")?;
            let [colon, type_syntax] = type_parts else {
                return Err(failure(SourceInferenceError::ExpectedType));
            };
            expect_atom(colon, ":", "binder type ascription")?;
            let domain = self.type_term(type_syntax)?;
            for name in names {
                let Syntax::Ident { val: name, .. } = name else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                let id = FVarId(self.fresh_name()?);
                self.txn
                    .lctx
                    .add_param(id.clone(), name.clone(), domain.clone(), style);
                parameters.push(self.txn.lctx.find(&id).expect("inserted parameter").clone());
            }
        }
        Ok(parameters)
    }
}

pub(super) fn definition(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
) -> Result<Declaration, NatDefinitionElabError> {
    let mut context = Context::new(environment, kernel);
    let declaration = expect_node(
        syntax,
        &parser_kind(&["Command", "declaration"]),
        2,
        "declaration",
    )?;
    let modifiers = expect_node(
        &declaration[0],
        &parser_kind(&["Command", "declModifiers"]),
        7,
        "declaration modifiers",
    )?;
    for modifier in modifiers {
        expect_empty_null(modifier, "empty declaration modifier")?;
    }
    let is_instance = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","instance"]));
    let is_theorem = matches!(&declaration[1], Syntax::Node { kind,.. } if kind==&parser_kind(&["Command","theorem"]));
    let instance_parts;
    let definition = if is_instance {
        let parts = instance_command::parts(&declaration[1])?;
        instance_parts = [
            parts.keyword.clone(),
            parts.id.clone(),
            parts.signature.clone(),
            parts.value.clone(),
        ];
        &instance_parts[..]
    } else {
        let parts = expect_node(
            &declaration[1],
            &parser_kind(&["Command", if is_theorem { "theorem" } else { "definition" }]),
            if is_theorem { 4 } else { 5 },
            "named declaration",
        )?;
        expect_atom(
            &parts[0],
            if is_theorem { "theorem" } else { "def" },
            "declaration keyword",
        )?;
        parts
    };
    let id = expect_node(
        &definition[1],
        &parser_kind(&["Command", "declId"]),
        2,
        "declaration id",
    )?;
    let Syntax::Ident { val: name, .. } = &id[0] else {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    };
    if name.is_anonymous() {
        return Err(NatDefinitionElabError::AnonymousDeclarationName);
    }
    expect_empty_null(&id[1], "absent declaration pre-parser")?;
    let signature = expect_node(
        &definition[2],
        &parser_kind(&[
            "Command",
            if is_theorem || is_instance {
                "declSig"
            } else {
                "optDeclSig"
            },
        ]),
        2,
        "declaration signature",
    )?;
    let parameters = context.bind_parameters(&signature[0])?;
    let expected = if is_theorem || is_instance {
        let parts = expect_node(
            &signature[1],
            &parser_kind(&["Term", "typeSpec"]),
            2,
            "theorem type",
        )?;
        expect_atom(&parts[0], ":", "theorem type colon")?;
        Some(context.type_term(&parts[1])?)
    } else {
        optional_type_syntax(&signature[1])?
            .map(|syntax| context.type_term(syntax))
            .transpose()?
    };
    let parts = expect_node(
        &definition[3],
        &parser_kind(&["Command", "declValSimple"]),
        4,
        "definition value",
    )?;
    expect_atom(&parts[0], ":=", "definition assignment")?;
    let termination = expect_node(
        &parts[2],
        &parser_kind(&["Termination", "suffix"]),
        2,
        "termination suffix",
    )?;
    for part in termination {
        expect_empty_null(part, "absent termination clause")?;
    }
    expect_empty_null(&parts[3], "absent where clause")?;
    if !is_theorem && !is_instance {
        expect_empty_null(&definition[4], "absent definition clauses")?;
    }
    if is_instance {
        context.validate_instance_binder(
            expected
                .as_ref()
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?,
        )?;
    }
    let mut term = context.term(&parts[1], expected.clone())?;
    if let Some(expected) = expected {
        term.type_ = expected;
    }
    let mut term = context.finish(term)?;
    term.value = eta_expand_nondependent(term.value, &term.type_)?;
    for local in parameters.into_iter().rev() {
        let LocalDecl {
            id,
            user_name: name,
            type_: domain,
            binder_info: style,
            ..
        } = local;
        let domain = context.instantiate(&domain)?;
        term.value = term
            .value
            .abstract_fvar(&id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        term.type_ = term
            .type_
            .abstract_fvar(&id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        term.value = Expr::lam(name.clone(), domain.clone(), term.value, style);
        term.type_ = Expr::forall_e(name, domain, term.type_, style);
    }
    let term = context.finish(term)?;
    if term.value.has_fvar()
        || term.type_.has_fvar()
        || term.value.has_loose_bvars()
        || term.type_.has_loose_bvars()
    {
        return Err(failure(SourceInferenceError::Scope));
    }
    let base = ConstantVal {
        name: name.clone(),
        level_params: Vec::new(),
        type_: term.type_,
    };
    if is_theorem {
        Ok(Declaration::Thm(fln_env::constants::TheoremVal {
            base,
            value: term.value,
            all: vec![name.clone()],
        }))
    } else {
        Ok(Declaration::Defn(DefinitionVal {
            base,
            value: term.value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        }))
    }
}

pub(super) fn query(
    syntax: &Syntax,
    name: Name,
    environment: &Environment,
    kernel: Budget,
    evaluate: bool,
) -> Result<Declaration, NatDefinitionElabError> {
    if !name.parent().is_anonymous() || !matches!(name.leaf_view(), LeafView::Num(_)) {
        return Err(if evaluate {
            NatDefinitionElabError::InvalidGeneratedEvaluationName
        } else {
            NatDefinitionElabError::InvalidGeneratedCheckName
        });
    }
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", if evaluate { "eval" } else { "check" }]),
        2,
        if evaluate {
            "Lean.Parser.Command.eval"
        } else {
            "Lean.Parser.Command.check"
        },
    )?;
    expect_atom(
        &parts[0],
        if evaluate { "#eval" } else { "#check" },
        "query keyword",
    )?;
    let mut context = Context::new(environment, kernel);
    let term = context.term(&parts[1], None)?;
    let mut term = context.finish(term)?;
    if evaluate {
        term.value = eta_expand_nondependent(term.value, &term.type_)?;
    }
    Ok(Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: term.type_,
        },
        value: term.value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name],
    }))
}

/// Registration requested by a canonical named source instance. The caller must
/// still obtain ordinary declaration admission before installing this metadata.
pub fn instance_registration(
    syntax: &Syntax,
) -> Result<Option<(Name, u32)>, NatDefinitionElabError> {
    instance_command::registration(syntax)
}

/// A source record/class expands to a block and projections, not one definition.
/// These are untrusted candidates. The caller must admit the whole sequence
/// before registering the class or exposing any successor.
pub use record::{SourceRecord, elaborate_record, is_record};
