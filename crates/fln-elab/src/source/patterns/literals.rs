//! Compact literal decisions within the ordered constructor-pattern matrix.
//!
//! A Boolean comparison never produces an equality witness. Original subject
//! types remain unchanged; dependent refinements still need the checked index
//! equation backend. Where a constructor split or structural root needs Nat's
//! fields, expose only one constructor layer and keep the predecessor compact.
use super::*;
use crate::tactic_macros::TacticMacroError;
use fln_bignum::nat::BigNat;
use fln_core::expr::{Literal, NatLit};

/// A Char pattern retains its domain even though Char.ofNat carries a Nat payload.
#[derive(Clone)]
enum Value {
    Nat(NatLit),
    String(String),
    Char(char),
}

fn literal_kind(kind: &Name) -> bool {
    ["num", "str", "char"]
        .iter()
        .any(|literal| *kind == Name::from_components([*literal]))
}

fn pattern_macro_depth(depth: usize) -> Result<usize, NatDefinitionElabError> {
    depth.checked_add(1).ok_or_else(|| {
        tactics::imported_macros::macro_error(TacticMacroError::Inconclusive(Box::new(
            fln_core::outcome::Inconclusive::dependency_unavailable(
                "pattern macro recursion depth overflow",
            ),
        )))
    })
}

pub(super) struct LiteralPattern<'a> {
    value: Value,
    syntax: Cow<'a, Syntax>,
}

impl Context {
    /// Literal canonicalization needs the metered arithmetic rung of Meta.whnf,
    /// not only the source head reducer's beta/delta/iota steps. This read-only
    /// query leaves metavariable assignments unchanged and honors transparency.
    fn finite_pattern_whnf(&mut self, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let budget = self.ambient_budget(UnificationTransparency::Default);
        let locals = self.txn.lctx.clone();
        self.txn
            .whnf_with(value, &locals, budget)
            .map_err(|error| failure(SourceInferenceError::Unification(Box::new(error))))
    }

    /// The name Fin alone does not authorize erasing a constructor field. Check
    /// the admitted constructor's complete type and its relation's Prop result
    /// before treating that field as the canonical numeric bound proof.
    fn check_finite_pattern_constructor(&mut self) -> Result<(), NatDefinitionElabError> {
        let unsupported = || {
            failure(SourceInferenceError::UnsupportedFinLiteralPattern(
                "the Fin constructor does not have the canonical bound proof",
            ))
        };
        let fin = Name::from_components(["Fin"]);
        let constructor = Name::from_components(["Fin", "mk"]);
        if !matches!(self.txn.env.find(&constructor), Some(ConstantInfo::Ctor(info))
            if info.induct == fin && info.num_params == 1 && info.num_fields == 2
                && info.base.level_params.is_empty())
        {
            return Err(unsupported());
        }
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let relation = Expr::const_(Name::from_components(["Nat", "lt"]), Vec::new());
        let relation_type = Expr::forall_e(
            Name::anonymous(),
            nat.clone(),
            Expr::forall_e(
                Name::anonymous(),
                nat.clone(),
                Expr::sort(Level::zero()),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let value = Expr::bvar(0).expect("fixed constructor binder");
        let bound = Expr::bvar(1).expect("fixed constructor binder");
        let proof = Expr::app(Expr::app(relation.clone(), value), bound);
        let result = Expr::app(
            Expr::const_(fin, Vec::new()),
            Expr::bvar(2).expect("fixed constructor binder"),
        );
        let constructor_type = Expr::forall_e(
            Name::anonymous(),
            nat.clone(),
            Expr::forall_e(
                Name::anonymous(),
                nat,
                Expr::forall_e(Name::anonymous(), proof, result, BinderInfo::Default),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        );
        for (value, expected) in [
            (relation, relation_type),
            (Expr::const_(constructor, Vec::new()), constructor_type),
        ] {
            match self.check_finite_pattern_term(value, expected) {
                Err(NatDefinitionElabError::Inference(SourceInferenceError::TypeObligation(
                    outcome,
                ))) if matches!(
                    outcome.as_ref(),
                    Outcome::Complete(Verdict::Rejected { .. })
                ) =>
                {
                    return Err(unsupported());
                }
                outcome => outcome?,
            }
        }
        Ok(())
    }

    /// Check a pattern term before literal canonicalization erases its
    /// dictionary. This query closes exactly its transitive local dependencies;
    /// it publishes no declaration and adds no executable term to the matcher.
    fn check_finite_pattern_term(
        &mut self,
        mut value: Expr,
        mut expected: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.require_resolved(&[value.clone(), expected.clone()])?;
        let mut needed = self.elimination_reads(&value)?;
        needed.extend(self.elimination_reads(&expected)?);
        for local in self.txn.lctx.decls().to_vec().into_iter().rev() {
            self.tick()?;
            if !needed.remove(&local.id) {
                continue;
            }
            let domain = self.instantiate(&local.type_)?;
            let definition = local
                .value
                .as_ref()
                .map(|v| self.instantiate(v))
                .transpose()?;
            self.require_resolved(std::slice::from_ref(&domain))?;
            needed.extend(self.elimination_reads(&domain)?);
            if let Some(definition) = &definition {
                self.require_resolved(std::slice::from_ref(definition))?;
                needed.extend(self.elimination_reads(definition)?);
            }
            let close = |term: &Expr| {
                term.abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))
            };
            let value_body = close(&value)?;
            let type_body = close(&expected)?;
            match definition {
                Some(definition) => {
                    value = Expr::let_e(
                        local.user_name.clone(),
                        domain.clone(),
                        definition.clone(),
                        value_body,
                        false,
                    );
                    expected = Expr::let_e(local.user_name, domain, definition, type_body, false);
                }
                None => {
                    value = Expr::lam(
                        local.user_name.clone(),
                        domain.clone(),
                        value_body,
                        local.binder_info,
                    );
                    expected =
                        Expr::forall_e(local.user_name, domain, type_body, local.binder_info);
                }
            }
        }
        if !needed.is_empty() || value.has_fvar() || expected.has_fvar() {
            return Err(invalid());
        }
        let name = loop {
            let name = self.fresh_name()?;
            if !self.txn.env.contains(&name) {
                break name;
            }
        };
        // The pin's Meta.check accepts unsafe dictionaries in literal patterns
        // that canonicalization erases. Use the kernel's existing unsafe body
        // typing mode only for this unpublished query, never for the matcher.
        let declaration = Declaration::Defn(fln_env::constants::DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: self.level_params.clone(),
                type_: expected,
            },
            value,
            hints: fln_env::constants::ReducibilityHints::Opaque,
            safety: fln_env::constants::DefinitionSafety::Unsafe,
            all: vec![name],
        });
        let remaining = if self.txn.budget.max_heartbeats == 0 {
            u64::MAX
        } else {
            self.txn
                .budget
                .max_heartbeats
                .saturating_sub(self.txn.budget.heartbeats_consumed)
        };
        let outcome = fln_kernel::check(
            &self.txn.env,
            &declaration,
            self.kernel
                .narrowed(self.kernel.steps.min(remaining), self.kernel.depth),
        );
        let consumed = match &outcome {
            Outcome::Complete(Verdict::Accepted { consumption })
            | Outcome::Complete(Verdict::Rejected { consumption, .. }) => consumption.steps_used,
            Outcome::Inconclusive(problem) => match &problem.cause {
                fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
                    if matches!(usage.reason, fln_core::diag::ResourceReason::ExecutionSteps) =>
                {
                    usage.observed
                }
                _ => 0,
            },
            _ => 0,
        };
        self.txn.budget.heartbeats_consumed =
            self.txn.budget.heartbeats_consumed.saturating_add(consumed);
        match outcome {
            Outcome::Complete(Verdict::Accepted { .. }) => self.tick(),
            outcome => Err(failure(SourceInferenceError::TypeObligation(Box::new(
                outcome,
            )))),
        }
    }

    /// Match.getFinValue? canonicalizes a typed numeral modulo its closed
    /// bound. Require the original dictionary's actual value to agree as well:
    /// the pin retains that original value in a dependent RHS's expected type.
    fn finite_literal_value(
        &mut self,
        syntax: &Syntax,
        expected: &Expr,
    ) -> Result<NatLit, NatDefinitionElabError> {
        let unsupported =
            |reason| failure(SourceInferenceError::UnsupportedFinLiteralPattern(reason));
        let expected = self.instantiate(expected)?;
        if expected.has_expr_mvar() || expected.has_level_mvar() {
            return Err(unsupported("the discriminant type is not resolved"));
        }
        let reduced = self.whnf(&expected)?;
        let (head, arguments) = operators::spine(&reduced);
        let [bound] = arguments.as_slice() else {
            return Err(invalid());
        };
        if !matches!(head.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["Fin"]) && levels.is_empty())
        {
            return Err(invalid());
        }
        let bound = self.finite_pattern_whnf(bound)?;
        let ExprNode::Lit {
            literal: Literal::Nat(bound_value),
        } = bound.node()
        else {
            return Err(unsupported("the bound is not a closed natural number"));
        };
        let empty_bound = bound_value.limbs_le().is_empty();
        // Establish the bound in the original context. A trial cannot choose
        // it by assignments that would disappear when that trial is discarded.
        let mut trial = self.clone();
        trial.equations.clear();
        trial.stalled_flush = None;
        trial.instance_goals.clear();
        trial.bound_metavars.clear();
        trial.postponed_coercions.clear();
        trial.postponed_fields.clear();
        let result = (|| {
            // expandMacrosInPatterns has already visited this primitive leaf.
            let term = trial.atom(syntax, Some(&expected))?;
            trial.resolve_instances(true)?;
            trial.flush(true)?;
            let value = trial.instantiate(&term.value)?;
            trial.check_finite_pattern_term(value.clone(), expected)?;
            if empty_bound {
                return Err(unsupported("a literal at Fin 0"));
            }
            let (head, arguments) = operators::spine(&value);
            let [_, number, _] = arguments.as_slice() else {
                return Err(invalid());
            };
            if !matches!(head.node(), ExprNode::Const { name, .. }
                if name == &Name::from_components(["OfNat", "ofNat"]))
                || !matches!(
                    number.node(),
                    ExprNode::Lit {
                        literal: Literal::Nat(_)
                    }
                )
            {
                return Err(invalid());
            }
            let remainder = trial.finite_pattern_whnf(&Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["Nat", "mod"]), Vec::new()),
                    number.clone(),
                ),
                bound,
            ))?;
            let ExprNode::Lit {
                literal: Literal::Nat(number),
            } = remainder.node()
            else {
                return Err(unsupported("the canonical numeral does not reduce"));
            };
            // A changed dictionary needs a separate original RHS typing
            // witness. Never silently type its RHS against a different value.
            let actual = trial.finite_pattern_whnf(&value)?;
            let (head, arguments) = operators::spine(&actual);
            let [_, natural, _] = arguments.as_slice() else {
                return Err(unsupported(
                    "the OfNat dictionary does not expose a Fin constructor",
                ));
            };
            if !matches!(head.node(), ExprNode::Const { name, levels }
                if name == &Name::from_components(["Fin", "mk"]) && levels.is_empty())
            {
                return Err(unsupported(
                    "the OfNat dictionary does not expose a Fin constructor",
                ));
            }
            let natural = trial.finite_pattern_whnf(natural)?;
            let ExprNode::Lit {
                literal: Literal::Nat(natural),
            } = natural.node()
            else {
                return Err(unsupported(
                    "the OfNat dictionary's value is not a closed natural number",
                ));
            };
            if !trial
                .same_pattern_literal(&Value::Nat(number.clone()), &Value::Nat(natural.clone()))?
            {
                return Err(unsupported(
                    "the OfNat dictionary changes the canonical numeral",
                ));
            }
            Ok(number.clone())
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        result
    }

    /// Expose small constructors, and render larger numeric patterns with
    /// metered work per limb rather than allocating an unbounded unary tree.
    fn finite_literal_syntax(
        &mut self,
        natural: &NatLit,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if let Some(value) = natural.to_u64().filter(|value| *value <= 256) {
            let mut pattern = identifier(Name::from_components(["_root_", "Nat", "zero"]));
            for _ in 0..value {
                self.tick()?;
                pattern = Syntax::node(
                    parser_kind(&["Term", "app"]),
                    vec![
                        identifier(Name::from_components(["_root_", "Nat", "succ"])),
                        null(vec![pattern]),
                    ],
                );
            }
            return Ok(pattern);
        }
        let mut spelling = String::from("0x");
        for (position, limb) in natural.limbs_le().iter().rev().enumerate() {
            self.tick()?;
            use std::fmt::Write;
            if position == 0 {
                write!(&mut spelling, "{limb:x}").expect("String write");
            } else {
                write!(&mut spelling, "{limb:016x}").expect("String write");
            }
        }
        Ok(Syntax::node(
            Name::from_components(["num"]),
            vec![atom(&spelling)],
        ))
    }

    /// Read only the types of discriminants that already have local bindings.
    /// In particular, equation declarations open their complete telescope before
    /// preparing the matrix. Do not elaborate an arbitrary discriminant here:
    /// its macro effects and its runtime value still belong to the ordinary
    /// checked input binding, which is evaluated once.
    pub(super) fn finite_pattern_columns(
        &mut self,
        discriminants: &[&Syntax],
        patterns: &[Cow<'_, Syntax>],
    ) -> Result<Vec<Option<Expr>>, NatDefinitionElabError> {
        // Most matrices contain no numeral columns. In particular, do not
        // normalize their local types or trigger unrelated source constraints.
        let mut numeric = vec![false; discriminants.len()];
        for row in patterns {
            let [group] = expect_null_args(row, "one pattern row")? else {
                return Err(invalid());
            };
            let columns = sequence(group)?;
            if columns.len() != numeric.len() {
                return Err(invalid());
            }
            for (column, numeric) in columns.into_iter().zip(&mut numeric) {
                self.tick()?;
                *numeric |= column.kind() == Some(&Name::from_components(["num"]));
            }
        }
        let mut columns = Vec::with_capacity(discriminants.len());
        for (discriminant, numeric) in discriminants.iter().zip(numeric) {
            self.tick()?;
            if !numeric {
                columns.push(None);
                continue;
            }
            let parts = expect_node(
                discriminant,
                &parser_kind(&["Term", "matchDiscr"]),
                2,
                "discriminant",
            )?;
            let mut syntax = &parts[1];
            while let Some(inner) = parenthesized_inner(syntax)? {
                syntax = inner;
            }
            let type_ = if let Syntax::Ident {
                val, preresolved, ..
            } = syntax
                && preresolved.is_empty()
            {
                self.txn
                    .lctx
                    .find_by_user_name(val)
                    .map(|local| local.type_.clone())
            } else {
                None
            };
            let Some(type_) = type_ else {
                columns.push(None);
                continue;
            };
            let reduced = self.whnf(&type_)?;
            let finite = matches!(reduced.node(), ExprNode::App { f, .. }
                    if matches!(f.node(), ExprNode::Const { name, levels }
                        if name == &Name::from_components(["Fin"]) && levels.is_empty()));
            // Instance synthesis must see the original expected type. A
            // semireducible alias must not become transparent to class search.
            columns.push(finite.then_some(type_));
        }
        if columns.iter().any(Option::is_some) {
            self.check_finite_pattern_constructor()?;
        }
        Ok(columns)
    }

    /// The pin's `expandFinValuePattern` expands the canonical value returned
    /// by `getFinValue?`: `3 : Fin 3` therefore selects zero. Source instance
    /// typing is checked independently before this normalization erases it.
    /// The proof field is retained as a matrix column; it is the evidence that
    /// can make an otherwise missing Nat constructor genuinely unreachable.
    pub(super) fn expand_finite_pattern_row(
        &mut self,
        row: &Syntax,
        types: &[Option<Expr>],
    ) -> Result<Option<Syntax>, NatDefinitionElabError> {
        if types.iter().all(Option::is_none) {
            return Ok(None);
        }
        let [group] = expect_null_args(row, "one pattern row")? else {
            return Err(invalid());
        };
        let columns = sequence(group)?;
        if columns.len() != types.len() {
            return Err(invalid());
        }
        let mut changed = false;
        let mut expanded = Vec::new();
        for (index, (syntax, type_)) in columns.into_iter().zip(types).enumerate() {
            if index != 0 {
                expanded.push(atom(","));
            }
            let Some(type_) = type_
                .as_ref()
                .filter(|_| syntax.kind() == Some(&Name::from_components(["num"])))
            else {
                expanded.push(self.copy_pattern_syntax(syntax)?);
                continue;
            };
            let natural = self.finite_literal_value(syntax, type_)?;
            // A complete literal-only column has at most 256 rows. Expose its
            // small values as constructors so the existing dependent matcher
            // specializes the retained bound proof. Large sparse values keep
            // the compact literal decision path; never allocate a unary tree
            // proportional to an arbitrary-precision numeral.
            let natural = self.finite_literal_syntax(&natural)?;
            expanded.push(Syntax::node(
                parser_kind(&["Term", "app"]),
                vec![
                    identifier(Name::from_components(["_root_", "Fin", "mk"])),
                    null(vec![natural, wildcard()]),
                ],
            ));
            changed = true;
        }
        Ok(changed.then(|| null(vec![null(expanded)])))
    }

    /// Expand deferred literals before classifying any pattern in the row.
    /// `Term.expandMacrosInPatterns` uses `Lean.expandMacros`: macro results
    /// may be arbitrary pattern syntax, nodes expand before their children,
    /// and identifier leaves (including pattern binders) are never dispatched.
    /// Original compound nodes already passed through the source expansion
    /// pass; only generated compound nodes need that work again.
    pub(super) fn expand_pattern_macros<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Cow<'a, Syntax>, NatDefinitionElabError> {
        let Some(provider) = self.source_scope.tactic_macros.clone() else {
            return Ok(Cow::Borrowed(syntax));
        };
        enum Task {
            Visit(Syntax, usize, bool),
            Finish(Syntax, usize),
        }
        let mut pending = vec![Task::Visit(
            self.copy_pattern_syntax(syntax)?,
            self.tactic_macro_depth,
            false,
        )];
        let mut built = Vec::new();
        let tactic = parser_kind(&["Term", "byTactic"]);
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Finish(mut node, start) => {
                    let Syntax::Node { args, .. } = &mut node else {
                        unreachable!("only pattern nodes have finish tasks");
                    };
                    *args = built.split_off(start);
                    built.push(node);
                }
                Task::Visit(mut node, depth, generated) => {
                    let Some(kind) = node.kind() else {
                        built.push(node);
                        continue;
                    };
                    if *kind == tactic {
                        built.push(node);
                        continue;
                    }
                    if (generated || self.tactic_macro_terms > 0 || literal_kind(kind))
                        && let Some(expanded) = provider
                            .0
                            .expand_term(&node, depth, &self.txn.env, &self.source_scope)
                            .map_err(|error| match error {
                                TacticMacroError::Diagnostic {
                                    declaration,
                                    message,
                                } => failure(SourceInferenceError::PatternMacroDiagnostic {
                                    declaration,
                                    message,
                                }),
                                error => tactics::imported_macros::macro_error(error),
                            })?
                    {
                        pending.push(Task::Visit(expanded, pattern_macro_depth(depth)?, true));
                        continue;
                    }
                    // A quotation may introduce native list/tuple notation
                    // after the ordinary source lowering pass has visited it.
                    // Reuse that lowering; it only constructs source syntax.
                    if generated && collections::is_notation(&node) {
                        pending.push(Task::Visit(
                            self.expand_collection_node(node, true)?,
                            pattern_macro_depth(depth)?,
                            true,
                        ));
                        continue;
                    }
                    let Syntax::Node { args, .. } = &mut node else {
                        built.push(node);
                        continue;
                    };
                    let children = std::mem::take(args);
                    let child_depth = if generated {
                        pattern_macro_depth(depth)?
                    } else {
                        depth
                    };
                    pending.push(Task::Finish(node, built.len()));
                    pending.extend(
                        children
                            .into_iter()
                            .rev()
                            .map(|child| Task::Visit(child, child_depth, generated)),
                    );
                }
            }
        }
        Ok(Cow::Owned(built.pop().ok_or_else(invalid)?))
    }

    pub(super) fn decode_pattern_literal<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Option<LiteralPattern<'a>>, NatDefinitionElabError> {
        let Syntax::Node { kind, args, .. } = syntax else {
            return Ok(None);
        };
        let natural = kind == &Name::from_components(["num"]);
        let string = kind == &Name::from_components(["str"]);
        let character = kind == &Name::from_components(["char"]);
        if !natural && !string && !character {
            return Ok(None);
        }
        let [Syntax::Atom { val, .. }] = args.as_slice() else {
            return Err(invalid());
        };
        // Charge input size before decoding, including raw spelling and escapes.
        for _ in val.as_bytes() {
            self.tick()?;
        }
        let value = if natural {
            let Literal::Nat(number) = decode_natural(val)? else {
                return Err(invalid());
            };
            Value::Nat(number)
        } else if string {
            let Literal::Str(text) = decode_string(val)? else {
                return Err(invalid());
            };
            Value::String(text)
        } else {
            Value::Char(super::super::character::decode_character(val)?)
        };
        Ok(Some(LiteralPattern {
            value,
            syntax: Cow::Borrowed(syntax),
        }))
    }

    fn same_pattern_literal(
        &mut self,
        a: &Value,
        b: &Value,
    ) -> Result<bool, NatDefinitionElabError> {
        match (a, b) {
            (Value::Nat(a), Value::Nat(b)) => {
                if a.limbs_le().len() != b.limbs_le().len() {
                    return Ok(false);
                }
                for (a, b) in a.limbs_le().iter().zip(b.limbs_le()) {
                    self.tick()?;
                    if a != b {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Value::String(a), Value::String(b)) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.bytes().zip(b.bytes()) {
                    self.tick()?;
                    if a != b {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Value::Char(a), Value::Char(b)) => {
                self.tick()?;
                Ok(a == b)
            }
            _ => Err(invalid()),
        }
    }

    fn compact_predecessor(
        &mut self,
        value: &NatLit,
    ) -> Result<LiteralPattern<'static>, NatDefinitionElabError> {
        for _ in value.limbs_le() {
            self.tick()?;
        }
        let value = BigNat::from_limbs_le(value.limbs_le().to_vec()).sub(&BigNat::from_u64(1));
        let mut spelling = String::from("0x");
        if value.limbs_le().is_empty() {
            spelling.push('0');
        }
        for (position, limb) in value.limbs_le().iter().rev().enumerate() {
            self.tick()?;
            use std::fmt::Write;
            if position == 0 {
                write!(&mut spelling, "{limb:x}").expect("String write");
            } else {
                write!(&mut spelling, "{limb:016x}").expect("String write");
            }
        }
        Ok(LiteralPattern {
            value: Value::Nat(NatLit::from_limbs_le(value.limbs_le().to_vec())),
            syntax: Cow::Owned(Syntax::node(
                Name::from_components(["num"]),
                vec![atom(&spelling)],
            )),
        })
    }

    /// Either prepare one constructor layer in place, or return a typed Boolean
    /// decision's ordered hit/miss matrices. No branch is selected by evaluating
    /// a user discriminant during elaboration.
    #[allow(clippy::type_complexity)]
    pub(super) fn literal_matrix_split<'a>(
        &mut self,
        matrix: &mut Matrix<'a>,
        subject: &Name,
        arena: &mut Vec<Pattern<'a>>,
    ) -> Result<Option<(Syntax, Matrix<'a>, Matrix<'a>)>, NatDefinitionElabError> {
        let mut selected = None;
        let mut constructors = matrix.recursive_root;
        for row in &matrix.rows {
            self.tick()?;
            match &arena[row.patterns[0]] {
                Pattern::Literal(_) => {
                    selected.get_or_insert(row.patterns[0]);
                }
                Pattern::Constructor(_) => constructors = true,
                Pattern::Bind(_) => {}
                Pattern::Named { .. } => return Err(invalid()),
            }
        }
        let Some(selected) = selected else {
            return Ok(None);
        };
        let Pattern::Literal(literal) = &arena[selected] else {
            unreachable!()
        };
        let value = literal.value.clone();
        let syntax = self.copy_pattern_syntax(&literal.syntax)?;
        // A mixed-typed literal column must not become a silently dead branch.
        for row in &matrix.rows {
            self.tick()?;
            if let Pattern::Literal(other) = &arena[row.patterns[0]]
                && std::mem::discriminant(&value) != std::mem::discriminant(&other.value)
            {
                return Err(invalid());
            }
        }
        if constructors {
            if !matches!(value, Value::Nat(_)) {
                return Err(invalid());
            }
            let mut expanded = HashMap::new();
            for row in &mut matrix.rows {
                self.tick()?;
                let pattern = row.patterns[0];
                if let Some(index) = expanded.get(&pattern) {
                    row.patterns[0] = *index;
                    continue;
                }
                let Pattern::Literal(LiteralPattern {
                    value: Value::Nat(number),
                    ..
                }) = &arena[pattern]
                else {
                    continue;
                };
                let zero = number.limbs_le().is_empty();
                let fields = if zero {
                    Vec::new()
                } else {
                    let predecessor = self.compact_predecessor(number)?;
                    let index = arena.len();
                    arena.push(Pattern::Literal(predecessor));
                    vec![index]
                };
                let name = Name::from_components(["Nat", if zero { "zero" } else { "succ" }]);
                let index = arena.len();
                arena.push(Pattern::Constructor(Constructor {
                    head: Head {
                        relative: false,
                        name: name.clone(),
                    },
                    syntax: Cow::Owned(identifier(name)),
                    labels: vec![None; fields.len()],
                    fields,
                    ellipsis: false,
                    record: false,
                }));
                expanded.insert(pattern, index);
                row.patterns[0] = index;
            }
            return Ok(None);
        }
        let mut hit = Vec::new();
        let mut miss = Vec::new();
        for row in &matrix.rows {
            self.tick()?;
            let mut accepted = row.clone();
            match &arena[accepted.patterns.remove(0)] {
                Pattern::Literal(other) => {
                    if self.same_pattern_literal(&value, &other.value)? {
                        hit.push(accepted);
                    } else {
                        miss.push(row.clone());
                    }
                }
                Pattern::Bind(name) => {
                    if let Some(name) = name {
                        accepted.bindings.push((name.clone(), subject.clone()));
                    }
                    hit.push(accepted);
                    miss.push(row.clone());
                }
                Pattern::Constructor(_) | Pattern::Named { .. } => return Err(invalid()),
            }
        }
        // Nat and String are infinite domains. Keep an empty miss matrix as
        // an explicit missing-case obligation, not a chosen result. Only the
        // typed outer constructor match can establish that its entire fallback
        // is unreachable (relative constructor names have no family here).
        // A reachable miss still refuses even for a closed discriminant.
        let application = |function, arguments| {
            Syntax::node(
                parser_kind(&["Term", "app"]),
                vec![function, null(arguments)],
            )
        };
        // This operand is already decoded, including compact predecessors
        // created while splitting Nat constructors. It is compiler input now,
        // not a new source literal eligible for another macro expansion.
        let syntax = Syntax::node(
            parser_kind(&["Term", "flnPreparedPatternLiteral"]),
            vec![syntax],
        );
        let operands = vec![identifier(subject.clone()), syntax];
        let test = if matches!(value, Value::Nat(_)) {
            application(identifier(Name::from_components(["Nat", "beq"])), operands)
        } else {
            // CaseValues.caseValue at the pin uses decidable propositional
            // equality. BEq need not agree with equality, and the synthetic
            // seed's String.decEq has only an opaque Bool-valued signature.
            // Neither justifies value-pattern semantics. Ordinary elaboration
            // must synthesize Decidable (Eq x value) in the admitted environment;
            // no instance or kernel rule is installed here. The globals cannot
            // be captured by local or namespace binders.
            let global = |leaf| identifier(Name::from_components(["_root_", leaf]));
            application(
                identifier(Name::from_components(["_root_", "Decidable", "decide"])),
                vec![application(global("Eq"), operands)],
            )
        };
        let mut miss_subjects = vec![subject.clone()];
        miss_subjects.extend(matrix.subjects.iter().cloned());
        Ok(Some((
            test,
            Matrix {
                recursive_root: false,
                subjects: matrix.subjects.clone(),
                rows: hit,
            },
            Matrix {
                recursive_root: false,
                subjects: miss_subjects,
                rows: miss,
            },
        )))
    }
}
