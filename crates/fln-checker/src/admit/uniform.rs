//! Constructor-derived checking of data and propositional inductive families.
//!
//! Every expected minor and iota rule is rebuilt from the family and constructor
//! telescopes, never copied from the recursor being checked. Recursive fields
//! must use the original parameters and universes; indices may change. Their
//! actual index expressions determine every induction hypothesis and recursive
//! call. Strictly positive function-valued children retain their argument telescopes.
//! Nested occurrences under unrelated type constructors remain unsupported.
use super::*;
use crate::infer::LocalDeclaration;
use crate::term::{
    TermBudget, TermOutcome, copy_compact_subterm_with, raise_external_bounds_with,
    substitute_bound_with,
};
use std::collections::BTreeMap;

#[derive(Clone)]
struct Binder {
    name: WireName,
    style: BinderStyle,
    domain: WireExpr,
}
struct RecursiveField {
    field: usize,
    arguments: Vec<Binder>,
    indices: Vec<WireExpr>,
}
struct Constructor<'a> {
    entry: &'a ConstantEntry,
    fields: Vec<Binder>,
    /// Each index expression is scoped over parameters and fields BEFORE this
    /// recursive field, not the complete constructor telescope.
    recursive: Vec<RecursiveField>,
    result_indices: Vec<WireExpr>,
}
struct Shape<'a> {
    name: &'a WireName,
    levels: &'a [WireName],
    parameters: Vec<Binder>,
    indices: Vec<Binder>,
    constructors: Vec<Constructor<'a>>,
    motive_universe: Option<&'a WireName>,
}
struct Audit<'a> {
    budget: AdmissionBudget,
    comparison: &'a mut StructuralComparisonControl,
    cancelled: &'a mut dyn FnMut() -> bool,
}

fn overflow() -> InductiveVerdict {
    InductiveVerdict::InternalFault(InductiveFault::ExpectedArenaOverflow)
}
fn arena_limit(observed: usize) -> InductiveVerdict {
    InductiveVerdict::Deferred(InductiveSupportLimit::ExpectedArenaUnits {
        observed,
        limit: MAX_INDUCTIVE_EXPECTED_ARENA_UNITS,
    })
}
fn constructor_error(name: &WireName) -> InductiveVerdict {
    InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { name: name.clone() })
}
fn recursor_error(name: &WireName) -> InductiveVerdict {
    InductiveVerdict::Rejected(InductiveRejection::RecursorShape { name: name.clone() })
}
fn size(term: &WireExpr) -> usize {
    term.nodes().len().saturating_add(term.levels().len())
}

/// A sufficient, independently computed positivity test for the result sort.
/// Sort u (which may be Prop) stays on its separate elimination-policy routes.
pub(super) fn positive_result(declaration: &ConstantDeclaration, count: u32) -> bool {
    let term = declaration.type_();
    if count as usize > MAX_NONRECURSIVE_FIELDS || size(term) > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
        return false;
    }
    let Some((_, tail)) = peel_binders_at(term, term.root(), count as usize) else {
        return false;
    };
    let Some(ExprNode::Sort { level }) = term.node(tail) else {
        return false;
    };
    let Ok(normal) = normalize(&WireLevel::from_parts(term.levels().to_vec(), *level)) else {
        return false;
    };
    let mut positive = Vec::with_capacity(normal.nodes().len());
    for node in normal.nodes() {
        let yes = match node {
            NormalNode::Succ(_) => true,
            NormalNode::Max(a, b) => positive[a.index()] || positive[b.index()],
            NormalNode::IMax(_, b) => positive[b.index()],
            NormalNode::Zero | NormalNode::Parameter(_) | NormalNode::Meta(_) => false,
        };
        positive.push(yes);
    }
    positive[normal.root().index()]
}

/// The generic predicate route is selected only at a definitely zero sort.
/// Sort u, whose proposition/data status can vary, keeps its existing routes.
pub(super) fn proposition_result(declaration: &ConstantDeclaration, count: u32) -> bool {
    let term = declaration.type_();
    if count as usize > MAX_NONRECURSIVE_FIELDS || size(term) > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
        return false;
    }
    let Some((_, tail)) = peel_binders_at(term, term.root(), count as usize) else {
        return false;
    };
    let Some(ExprNode::Sort { level }) = term.node(tail) else {
        return false;
    };
    normalize(&WireLevel::from_parts(term.levels().to_vec(), *level))
        .ok()
        .and_then(|n| explicit_normal_universe(&n))
        == Some(0)
}

impl Audit<'_> {
    fn tick(&mut self) -> Result<(), InductiveVerdict> {
        self.comparison
            .comparison(self.cancelled)
            .map_err(|stop| InductiveVerdict::Inconclusive(InductiveStop::Structural(stop)))
    }
    fn term_budget(&self) -> TermBudget {
        let budget = self.budget.inference.materialization;
        TermBudget {
            max_arena_nodes: budget
                .max_arena_nodes
                .min(MAX_INDUCTIVE_EXPECTED_ARENA_UNITS as u64),
            max_output_units: budget
                .max_output_units
                .min(MAX_INDUCTIVE_EXPECTED_ARENA_UNITS as u64),
            ..budget
        }
    }
    fn term(result: TermOutcome<WireExpr>) -> Result<WireExpr, InductiveVerdict> {
        match result {
            TermOutcome::Complete(term) => Ok(term),
            TermOutcome::Inconclusive(stop) => {
                Err(InductiveVerdict::Inconclusive(InductiveStop::Term(stop)))
            }
            TermOutcome::InternalFault(fault) => {
                Err(InductiveVerdict::InternalFault(InductiveFault::Term(fault)))
            }
        }
    }
    fn piece(&mut self, source: &WireExpr, root: ExprId) -> Result<WireExpr, InductiveVerdict> {
        self.tick()?;
        Self::term(copy_compact_subterm_with(
            source,
            root,
            self.term_budget(),
            self.cancelled,
        ))
    }
    fn equal(&mut self, actual: &WireExpr, expected: &WireExpr) -> Result<bool, InductiveVerdict> {
        compare_inductive_expression(actual, expected, self.comparison, self.cancelled)
    }
    fn peel(
        &mut self,
        source: &WireExpr,
        count: usize,
    ) -> Result<(Vec<Binder>, WireExpr), InductiveVerdict> {
        let mut tail = source.root();
        let mut binders = Vec::with_capacity(count);
        for _ in 0..count {
            self.tick()?;
            let Some(ExprNode::Forall {
                binder_name,
                binder_type,
                body,
                style,
            }) = source.node(tail)
            else {
                return Err(InductiveVerdict::Deferred(
                    InductiveSupportLimit::ResultUniverse,
                ));
            };
            binders.push(Binder {
                name: binder_name.clone(),
                style: *style,
                domain: self.piece(source, *binder_type)?,
            });
            tail = *body;
        }
        Ok((binders, self.piece(source, tail)?))
    }
    fn import(
        &mut self,
        builder: &mut StructuralTermBuilder,
        term: &WireExpr,
    ) -> Result<ExprId, InductiveVerdict> {
        self.tick()?;
        let units = builder
            .nodes
            .len()
            .saturating_add(builder.levels.len())
            .saturating_add(size(term));
        if units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
            return Err(arena_limit(units));
        }
        builder.import(term, term.root()).ok_or_else(overflow)
    }
    fn shifted(
        &mut self,
        builder: &mut StructuralTermBuilder,
        term: &WireExpr,
        amount: usize,
        cutoff: usize,
    ) -> Result<ExprId, InductiveVerdict> {
        self.tick()?;
        let term = Self::term(raise_external_bounds_with(
            term,
            amount as u32,
            cutoff as u32,
            self.term_budget(),
            &mut *self.cancelled,
        ))?;
        self.import(builder, &term)
    }
    /// Insert recursor binders between parameters and a constructor's fields,
    /// then append the later fields/hypotheses. Separate cutoffs preserve
    /// dependencies within the original constructor telescope.
    fn relocated(
        &mut self,
        builder: &mut StructuralTermBuilder,
        term: &WireExpr,
        fields: usize,
        recursor_binders: usize,
        later: usize,
    ) -> Result<ExprId, InductiveVerdict> {
        self.tick()?;
        let term = Self::term(raise_external_bounds_with(
            term,
            recursor_binders as u32,
            fields as u32,
            self.term_budget(),
            &mut *self.cancelled,
        ))?;
        self.shifted(builder, &term, later, 0)
    }
    /// Relocate the ambient telescope without moving the function's own
    /// arguments. Both shifts keep those innermost bounds fixed.
    fn relocated_under(
        &mut self,
        builder: &mut StructuralTermBuilder,
        term: &WireExpr,
        fields: usize,
        recursor_binders: usize,
        later: usize,
        inner: usize,
    ) -> Result<ExprId, InductiveVerdict> {
        self.tick()?;
        let term = Self::term(raise_external_bounds_with(
            term,
            recursor_binders as u32,
            (fields + inner) as u32,
            self.term_budget(),
            &mut *self.cancelled,
        ))?;
        self.shifted(builder, &term, later, inner)
    }

    fn recursive_field(
        &mut self,
        term: &WireExpr,
        name: &WireName,
        levels: &[WireName],
        parameters: usize,
        field: usize,
        indices: usize,
    ) -> Result<Option<RecursiveField>, InductiveVerdict> {
        let mut tail = term.root();
        let mut count = 0usize;
        loop {
            self.tick()?;
            match term.node(tail) {
                Some(ExprNode::Metadata { expression, .. }) => tail = *expression,
                Some(ExprNode::Forall {
                    binder_type, body, ..
                }) => {
                    // Strict positivity forbids the family in *any* function
                    // domain, even if the final codomain is a valid occurrence.
                    let probe = ConstructorField {
                        source: term,
                        name,
                        style: BinderStyle::Default,
                        type_root: *binder_type,
                    };
                    if field_mentions_inductive(&probe, name, self.comparison, self.cancelled)? {
                        return Err(constructor_error(name));
                    }
                    count = count.saturating_add(1);
                    if count > MAX_NONRECURSIVE_FIELDS {
                        return Err(InductiveVerdict::Deferred(
                            InductiveSupportLimit::FieldCount {
                                observed: count,
                                limit: MAX_NONRECURSIVE_FIELDS,
                            },
                        ));
                    }
                    tail = *body;
                }
                _ => break,
            }
        }
        let result = self.piece(term, tail)?;
        let Some(indices) =
            self.family_indices(&result, name, levels, parameters, field + count, indices)?
        else {
            return Ok(None);
        };
        // Rebuild each argument domain at its own lexical depth. Metadata on
        // telescope nodes is transparent, but no binder is silently skipped.
        let mut arguments = Vec::with_capacity(count);
        let mut cursor = term.root();
        while arguments.len() < count {
            self.tick()?;
            match term.node(cursor) {
                Some(ExprNode::Metadata { expression, .. }) => cursor = *expression,
                Some(ExprNode::Forall {
                    binder_name,
                    binder_type,
                    body,
                    style,
                }) => {
                    arguments.push(Binder {
                        name: binder_name.clone(),
                        style: *style,
                        domain: self.piece(term, *binder_type)?,
                    });
                    cursor = *body;
                }
                _ => return Err(constructor_error(name)),
            }
        }
        Ok(Some(RecursiveField {
            field,
            arguments,
            indices,
        }))
    }

    #[allow(clippy::too_many_arguments)]
    fn family_indices(
        &mut self,
        term: &WireExpr,
        name: &WireName,
        levels: &[WireName],
        parameters: usize,
        fields: usize,
        indices: usize,
    ) -> Result<Option<Vec<WireExpr>>, InductiveVerdict> {
        let mut root = term.root();
        let mut arguments = Vec::with_capacity(indices);
        for _ in 0..indices {
            self.tick()?;
            while let Some(ExprNode::Metadata { expression, .. }) = term.node(root) {
                self.tick()?;
                root = *expression;
            }
            let Some(ExprNode::Apply { function, argument }) = term.node(root) else {
                return Ok(None);
            };
            arguments.push(self.piece(term, *argument)?);
            root = *function;
        }
        let mut builder = StructuralTermBuilder::new();
        let expected = application(&mut builder, name, levels, parameters, fields);
        let expected = self.finish(builder, expected)?;
        let prefix = self.piece(term, root)?;
        if !self.equal(&prefix, &expected)? {
            return Ok(None);
        }
        for argument in &arguments {
            let probe = ConstructorField {
                source: argument,
                name,
                style: BinderStyle::Default,
                type_root: argument.root(),
            };
            if field_mentions_inductive(&probe, name, self.comparison, self.cancelled)? {
                return Ok(None);
            }
        }
        arguments.reverse();
        Ok(Some(arguments))
    }
    fn open(
        &mut self,
        term: &WireExpr,
        locals: &[LocalDeclaration],
    ) -> Result<WireExpr, InductiveVerdict> {
        let mut term = term.clone();
        for local in locals.iter().rev() {
            self.tick()?;
            let mut builder = StructuralTermBuilder::new();
            let root = builder.expression(ExprNode::Free {
                name: local.name().clone(),
            });
            let value = builder.finish(root).ok_or_else(overflow)?;
            term = Self::term(substitute_bound_with(
                &term,
                0,
                &value,
                self.term_budget(),
                &mut *self.cancelled,
            ))?;
        }
        Ok(term)
    }
    fn append_local(
        &mut self,
        locals: &mut Vec<LocalDeclaration>,
        domain: &WireExpr,
    ) -> Result<WireExpr, InductiveVerdict> {
        let open = self.open(domain, locals)?;
        let name = checker_child(
            &checker_atom("_fln_uniform_parameter"),
            &locals.len().to_string(),
        );
        locals.push(LocalDeclaration::assumption(name, open.clone()));
        Ok(open)
    }
    fn finish(
        &mut self,
        builder: StructuralTermBuilder,
        root: ExprId,
    ) -> Result<WireExpr, InductiveVerdict> {
        self.tick()?;
        let units = builder.nodes.len().saturating_add(builder.levels.len());
        if units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
            return Err(arena_limit(units));
        }
        builder.finish(root).ok_or_else(overflow)
    }
}

fn application(
    builder: &mut StructuralTermBuilder,
    name: &WireName,
    levels: &[WireName],
    parameters: usize,
    offset: usize,
) -> ExprId {
    let mut result = builder.constant(name, levels);
    for index in 0..parameters {
        let parameter = builder.bvar((parameters + offset - index - 1) as u32);
        result = builder.apply(result, parameter);
    }
    result
}

impl Shape<'_> {
    fn motive(
        &self,
        audit: &mut Audit<'_>,
        builder: &mut StructuralTermBuilder,
    ) -> Result<ExprId, InductiveVerdict> {
        let q = self.indices.len();
        let mut family = application(builder, self.name, self.levels, self.parameters.len(), q);
        for index in 0..q {
            let value = builder.bvar((q - index - 1) as u32);
            family = builder.apply(family, value);
        }
        let sort = match self.motive_universe {
            Some(level) => builder.sort_parameter(level),
            None => builder.sort_zero(),
        };
        let mut body = builder.forall("major", BinderStyle::Default, family, sort);
        for index in self.indices.iter().rev() {
            let domain = audit.import(builder, &index.domain)?;
            body = builder.forall_name(&index.name, index.style, domain, body);
        }
        Ok(body)
    }
    fn minor(
        &self,
        audit: &mut Audit<'_>,
        builder: &mut StructuralTermBuilder,
        index: usize,
    ) -> Result<ExprId, InductiveVerdict> {
        let ctor = &self.constructors[index];
        let f = ctor.fields.len();
        let r = ctor.recursive.len();
        let mut constructed = application(
            builder,
            ctor.entry.name(),
            self.levels,
            self.parameters.len(),
            1 + index + f + r,
        );
        for field in 0..f {
            let value = builder.bvar((f + r - field - 1) as u32);
            constructed = builder.apply(constructed, value);
        }
        let mut motive = builder.bvar((index + f + r) as u32);
        for result in &ctor.result_indices {
            let value = audit.relocated(builder, result, f, 1 + index, r)?;
            motive = builder.apply(motive, value);
        }
        let mut body = builder.apply(motive, constructed);
        for (ih, recursive) in ctor.recursive.iter().enumerate().rev() {
            let field = recursive.field;
            let arity = recursive.arguments.len();
            let mut motive = builder.bvar((index + f + ih + arity) as u32);
            for child_index in &recursive.indices {
                let value = audit.relocated_under(
                    builder,
                    child_index,
                    field,
                    1 + index,
                    f - field + ih,
                    arity,
                )?;
                motive = builder.apply(motive, value);
            }
            let mut value = builder.bvar((f + ih + arity - field - 1) as u32);
            for argument in 0..arity {
                let local = builder.bvar((arity - argument - 1) as u32);
                value = builder.apply(value, local);
            }
            let mut domain = builder.apply(motive, value);
            for (position, argument) in recursive.arguments.iter().enumerate().rev() {
                let ty = audit.relocated_under(
                    builder,
                    &argument.domain,
                    field,
                    1 + index,
                    f - field + ih,
                    position,
                )?;
                domain = builder.forall_name(&argument.name, argument.style, ty, domain);
            }
            body = builder.forall("ih", BinderStyle::Default, domain, body);
        }
        for (field, binder) in ctor.fields.iter().enumerate().rev() {
            // Insert motive + previous minors OUTSIDE all preceding fields.
            // A dependent field's references to those fields must not move.
            let domain = audit.shifted(builder, &binder.domain, 1 + index, field)?;
            body = builder.forall_name(&binder.name, binder.style, domain, body);
        }
        Ok(body)
    }
    fn recursor_type(
        &self,
        audit: &mut Audit<'_>,
        styles: &[BinderStyle],
    ) -> Result<WireExpr, InductiveVerdict> {
        let mut builder = StructuralTermBuilder::new();
        let n = self.constructors.len();
        let p = self.parameters.len();
        let q = self.indices.len();
        let mut motive = builder.bvar((n + q + 1) as u32);
        for index in 0..q {
            let value = builder.bvar((q - index) as u32);
            motive = builder.apply(motive, value);
        }
        let major = builder.bvar(0);
        let body = builder.apply(motive, major);
        let mut major_type = application(&mut builder, self.name, self.levels, p, 1 + n + q);
        for index in 0..q {
            let value = builder.bvar((q - index - 1) as u32);
            major_type = builder.apply(major_type, value);
        }
        let mut body = builder.forall("major", styles[p + n + q + 1], major_type, body);
        for (index, binder) in self.indices.iter().enumerate().rev() {
            let domain = audit.shifted(&mut builder, &binder.domain, n + 1, index)?;
            body = builder.forall_name(&binder.name, styles[p + n + 1 + index], domain, body);
        }
        for index in (0..n).rev() {
            let domain = self.minor(audit, &mut builder, index)?;
            body = builder.forall("minor", styles[p + 1 + index], domain, body);
        }
        let motive_type = self.motive(audit, &mut builder)?;
        body = builder.forall("motive", styles[p], motive_type, body);
        for (index, parameter) in self.parameters.iter().enumerate().rev() {
            let domain = audit.import(&mut builder, &parameter.domain)?;
            body = builder.forall_name(&parameter.name, styles[index], domain, body);
        }
        audit.finish(builder, body)
    }
    fn rule(
        &self,
        audit: &mut Audit<'_>,
        index: usize,
        recursor_name: &WireName,
    ) -> Result<WireExpr, InductiveVerdict> {
        let mut builder = StructuralTermBuilder::new();
        let ctor = &self.constructors[index];
        let n = self.constructors.len();
        let f = ctor.fields.len();
        let mut body = builder.bvar((f + n - index - 1) as u32);
        for field in 0..f {
            let value = builder.bvar((f - field - 1) as u32);
            body = builder.apply(body, value);
        }
        let mut levels: Vec<_> = self.motive_universe.into_iter().cloned().collect();
        levels.extend_from_slice(self.levels);
        for recursive in &ctor.recursive {
            let field = recursive.field;
            let arity = recursive.arguments.len();
            let mut call = application(
                &mut builder,
                recursor_name,
                &levels,
                self.parameters.len(),
                f + n + 1 + arity,
            );
            let motive = builder.bvar((f + n + arity) as u32);
            call = builder.apply(call, motive);
            for minor in 0..n {
                let value = builder.bvar((f + n + arity - minor - 1) as u32);
                call = builder.apply(call, value);
            }
            for child_index in &recursive.indices {
                let value = audit.relocated_under(
                    &mut builder,
                    child_index,
                    field,
                    n + 1,
                    f - field,
                    arity,
                )?;
                call = builder.apply(call, value);
            }
            let mut value = builder.bvar((f + arity - field - 1) as u32);
            for argument in 0..arity {
                let local = builder.bvar((arity - argument - 1) as u32);
                value = builder.apply(value, local);
            }
            call = builder.apply(call, value);
            for (position, argument) in recursive.arguments.iter().enumerate().rev() {
                let domain = audit.relocated_under(
                    &mut builder,
                    &argument.domain,
                    field,
                    n + 1,
                    f - field,
                    position,
                )?;
                call = builder.lambda_name(&argument.name, argument.style, domain, call);
            }
            body = builder.apply(body, call);
        }
        for (field, binder) in ctor.fields.iter().enumerate().rev() {
            let domain = audit.shifted(&mut builder, &binder.domain, n + 1, field)?;
            body = builder.lambda_name(&binder.name, binder.style, domain, body);
        }
        for minor in (0..n).rev() {
            let domain = self.minor(audit, &mut builder, minor)?;
            body = builder.lambda("minor", BinderStyle::Default, domain, body);
        }
        let motive = self.motive(audit, &mut builder)?;
        body = builder.lambda("motive", BinderStyle::Default, motive, body);
        for parameter in self.parameters.iter().rev() {
            let domain = audit.import(&mut builder, &parameter.domain)?;
            body = builder.lambda_name(&parameter.name, parameter.style, domain, body);
        }
        audit.finish(builder, body)
    }
}

/// A sound sufficient universe inequality, not a full solver. Both normalized
/// DAGs are independent checker values. imax a b is bounded above by max a b
/// and below by b; using either bound cannot admit an oversized field.
fn universe_within(
    required: &WireLevel,
    allowed: &WireLevel,
    audit: &mut Audit<'_>,
) -> Result<bool, InductiveVerdict> {
    let left = normalize(required).map_err(|_| overflow())?;
    let right = normalize(allowed).map_err(|_| overflow())?;
    if left.structurally_equals(&right) {
        return Ok(true);
    }
    let mut done = BTreeMap::new();
    let root = (left.root().index(), right.root().index());
    let mut pending = vec![(root, false)];
    while let Some(((l, r), exit)) = pending.pop() {
        audit.tick()?;
        if done.contains_key(&(l, r)) {
            continue;
        }
        if done.len().saturating_add(pending.len()) > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
            return Err(arena_limit(done.len().saturating_add(pending.len())));
        }
        let mut dependencies = Vec::new();
        let mut all = true;
        let fixed = match (&left.nodes()[l], &right.nodes()[r]) {
            (NormalNode::Zero, _) => Some(true),
            (NormalNode::Parameter(a), NormalNode::Parameter(b)) if a == b => Some(true),
            (NormalNode::Meta(a), NormalNode::Meta(b)) if a == b => Some(true),
            (NormalNode::Succ(a), NormalNode::Succ(b)) => {
                dependencies.push((a.index(), b.index()));
                None
            }
            (NormalNode::Max(a, b) | NormalNode::IMax(a, b), _) => {
                dependencies.extend([(a.index(), r), (b.index(), r)]);
                None
            }
            (_, NormalNode::Max(a, b)) => {
                dependencies.extend([(l, a.index()), (l, b.index())]);
                all = false;
                None
            }
            (_, NormalNode::Succ(b) | NormalNode::IMax(_, b)) => {
                dependencies.push((l, b.index()));
                None
            }
            _ => Some(false),
        };
        if let Some(value) = fixed {
            done.insert((l, r), value);
        } else if exit {
            let value = if all {
                dependencies
                    .iter()
                    .all(|pair| done.get(pair) == Some(&true))
            } else {
                dependencies
                    .iter()
                    .any(|pair| done.get(pair) == Some(&true))
            };
            done.insert((l, r), value);
        } else {
            pending.push(((l, r), true));
            pending.extend(dependencies.into_iter().rev().map(|pair| (pair, false)));
        }
    }
    Ok(done.get(&root) == Some(&true))
}

pub(super) fn admit(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let mut audit = Audit {
        budget,
        comparison,
        cancelled,
    };
    match check(
        environment,
        declarations,
        inductive,
        environment_budget,
        &mut audit,
    ) {
        Ok(members) => InductiveVerdict::Admitted(InductiveAdmission { members }),
        Err(verdict) => verdict,
    }
}

#[allow(clippy::too_many_lines)]
fn check(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    environment_budget: EnvironmentBudget,
    audit: &mut Audit<'_>,
) -> Result<Vec<WireName>, InductiveVerdict> {
    audit.tick()?;
    let name = inductive.name();
    let declaration = inductive.declaration();
    let metadata = declaration
        .inductive_metadata()
        .ok_or_else(|| constructor_error(name))?;
    if metadata.mutual() != std::slice::from_ref(name) {
        return Err(InductiveVerdict::Deferred(
            InductiveSupportLimit::MutualMetadata,
        ));
    }
    if metadata.num_nested() != 0 {
        return Err(InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
            observed: metadata.num_nested(),
        }));
    }
    let levels = declaration.level_parameters();
    if levels.len() > 8 {
        return Err(InductiveVerdict::Deferred(
            InductiveSupportLimit::UniverseParameters {
                observed: levels.len(),
            },
        ));
    }
    let p = metadata.num_parameters() as usize;
    let q = metadata.num_indices() as usize;
    if p.saturating_add(q) > MAX_NONRECURSIVE_FIELDS {
        return Err(InductiveVerdict::Deferred(
            InductiveSupportLimit::FieldCount {
                observed: p.saturating_add(q),
                limit: MAX_NONRECURSIVE_FIELDS,
            },
        ));
    }
    let n = metadata.constructors().len();
    if n > MAX_NONRECURSIVE_CONSTRUCTORS {
        return Err(InductiveVerdict::Deferred(
            InductiveSupportLimit::ConstructorCount {
                observed: n,
                limit: MAX_NONRECURSIVE_CONSTRUCTORS,
            },
        ));
    }
    if declarations.len() != n + 2 {
        return Err(InductiveVerdict::Rejected(
            InductiveRejection::DeclarationCount {
                observed: declarations.len(),
                expected: n + 2,
            },
        ));
    }
    let mut names = BTreeSet::new();
    let mut input_units = 0usize;
    for entry in declarations {
        audit.tick()?;
        if !names.insert(entry.name()) || environment.find(entry.name()).is_some() {
            return Err(InductiveVerdict::Rejected(
                InductiveRejection::NameAlreadyDeclared {
                    name: entry.name().clone(),
                },
            ));
        }
        input_units = input_units.saturating_add(size(entry.declaration().type_()));
        if input_units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
            return Err(arena_limit(input_units));
        }
        if let Some(rec) = entry.declaration().recursor_metadata() {
            // Validate cardinality before walking untrusted rule tables. The
            // bounded constructor count must also bound metadata-only work.
            if rec.rules().len() != n {
                return Err(recursor_error(entry.name()));
            }
            for rule in rec.rules() {
                audit.tick()?;
                input_units = input_units.saturating_add(size(rule.rhs()));
                if input_units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
                    return Err(arena_limit(input_units));
                }
            }
        }
    }
    if input_units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
        return Err(arena_limit(input_units));
    }
    declared_type_is_a_type(
        environment,
        name,
        declaration,
        &audit.budget,
        audit.cancelled,
    )
    .map_err(|v| map_member_preamble(name, v))?;
    let (parameters, index_tail) = audit.peel(declaration.type_(), p)?;
    let (indices, result_sort) = audit.peel(&index_tail, q)?;
    let Some(ExprNode::Sort { level }) = result_sort.node(result_sort.root()) else {
        return Err(overflow());
    };
    let result_level = WireLevel::from_parts(result_sort.levels().to_vec(), *level);
    let proposition = normalize(&result_level)
        .ok()
        .and_then(|n| explicit_normal_universe(&n))
        == Some(0);
    let mut large_elimination = !proposition || n <= 1;
    let mut staged =
        stage_inductive_member(environment, inductive, environment_budget, audit.cancelled)?;
    let mut locals = Vec::new();
    for parameter in &parameters {
        audit.append_local(&mut locals, &parameter.domain)?;
    }
    let mut constructors = Vec::with_capacity(n);
    let mut seen_constructors = BTreeSet::new();
    let mut total_fields = 0usize;
    for (index, ctor_name) in metadata.constructors().iter().enumerate() {
        audit.tick()?;
        if !seen_constructors.insert(ctor_name) {
            return Err(InductiveVerdict::Rejected(
                InductiveRejection::RepeatedConstructor {
                    name: ctor_name.clone(),
                },
            ));
        }
        let entry = declarations
            .iter()
            .find(|entry| entry.name() == ctor_name)
            .ok_or_else(|| {
                InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                    name: ctor_name.clone(),
                })
            })?;
        let decl = entry.declaration();
        let cm = decl
            .constructor_metadata()
            .ok_or_else(|| constructor_error(ctor_name))?;
        let f = cm.num_fields() as usize;
        total_fields = total_fields.saturating_add(f);
        if total_fields > MAX_NONRECURSIVE_FIELDS {
            return Err(InductiveVerdict::Deferred(
                InductiveSupportLimit::FieldCount {
                    observed: total_fields,
                    limit: MAX_NONRECURSIVE_FIELDS,
                },
            ));
        }
        if decl.safety() != ConstantSafety::Safe
            || decl.level_parameters() != levels
            || cm.inductive() != name
            || cm.index() as usize != index
            || cm.num_parameters() as usize != p
        {
            return Err(constructor_error(ctor_name));
        }
        // This closed check rejects unknown/free names before generated local
        // identities are introduced for field-level universe checking.
        declared_type_is_a_type(&staged, ctor_name, decl, &audit.budget, audit.cancelled)
            .map_err(|v| map_member_preamble(ctor_name, v))?;
        let (ctor_params, field_tail) = audit.peel(decl.type_(), p)?;
        for (actual, expected) in ctor_params.iter().zip(&parameters) {
            if !audit.equal(&actual.domain, &expected.domain)? {
                return Err(constructor_error(ctor_name));
            }
        }
        if peel_binders_at(&field_tail, field_tail.root(), f).is_none() {
            return Err(constructor_error(ctor_name));
        }
        let (fields, result) = audit.peel(&field_tail, f)?;
        let result_indices = audit
            .family_indices(&result, name, levels, p, f, q)?
            .ok_or_else(|| constructor_error(ctor_name))?;
        let mut field_locals = locals.clone();
        let mut recursive = Vec::new();
        for (field_index, field) in fields.iter().enumerate() {
            if let Some(child) =
                audit.recursive_field(&field.domain, name, levels, p, field_index, q)?
            {
                recursive.push(child);
            } else {
                let probe = ConstructorField {
                    source: &field.domain,
                    name: &field.name,
                    style: field.style,
                    type_root: field.domain.root(),
                };
                if field_mentions_inductive(&probe, name, audit.comparison, audit.cancelled)? {
                    return Err(InductiveVerdict::Deferred(InductiveSupportLimit::Recursive));
                }
            }
            let open = audit.open(&field.domain, &field_locals)?;
            let context =
                InferenceContext::new(field_locals.clone(), levels.to_vec(), staged.clone())
                    .map_err(|_| overflow())?;
            let facts = type_is_type_in_context(
                ctor_name,
                &open,
                &context,
                ConstantSafety::Safe,
                &audit.budget,
                audit.cancelled,
            )
            .map_err(|v| map_member_preamble(ctor_name, v))?;
            // Prop is impredicative: the witness field itself may live at any
            // universe. This never licenses eliminating that witness into data.
            if proposition && n == 1 && facts.explicit_universe != Some(0) {
                let mut exposed = false;
                for index in &result_indices {
                    audit.tick()?;
                    if matches!(index.node(index.root()), Some(ExprNode::Bound { index })
                        if *index as usize == f - field_index - 1)
                    {
                        exposed = true;
                    }
                }
                large_elimination &= exposed;
            }
            if !proposition && !universe_within(&facts.universe, &result_level, audit)? {
                // The independent normalizer is deliberately incomplete. A
                // symbolic inequality it cannot establish is not a rejection.
                if facts.explicit_universe.is_some()
                    && normalize(&result_level)
                        .ok()
                        .and_then(|n| explicit_normal_universe(&n))
                        .is_some()
                {
                    return Err(constructor_error(ctor_name));
                }
                return Err(InductiveVerdict::Deferred(
                    InductiveSupportLimit::ResultUniverse,
                ));
            }
            audit.append_local(&mut field_locals, &field.domain)?;
        }
        staged = stage_inductive_member(&staged, entry, environment_budget, audit.cancelled)?;
        constructors.push(Constructor {
            entry,
            fields,
            recursive,
            result_indices,
        });
    }
    let reflexive = constructors
        .iter()
        .flat_map(|c| &c.recursive)
        .any(|field| !field.arguments.is_empty());
    if metadata.is_reflexive() != reflexive
        || metadata.is_recursive() != constructors.iter().any(|c| !c.recursive.is_empty())
    {
        return Err(constructor_error(name));
    }
    let rec_name = checker_child(name, "rec");
    let rec_entry = declarations
        .iter()
        .find(|e| e.name() == &rec_name)
        .ok_or_else(|| {
            InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
                name: rec_name.clone(),
            })
        })?;
    let rec_decl = rec_entry.declaration();
    let rec = rec_decl
        .recursor_metadata()
        .ok_or_else(|| recursor_error(&rec_name))?;
    let rec_levels = rec_decl.level_parameters();
    let level_policy = if large_elimination {
        rec_levels.len() == levels.len() + 1
            && &rec_levels[1..] == levels
            && !levels.contains(&rec_levels[0])
    } else {
        rec_levels == levels
    };
    let k_target = proposition && n == 1 && constructors[0].fields.is_empty();
    if rec_decl.safety() != ConstantSafety::Safe
        || !level_policy
        || rec.mutual() != std::slice::from_ref(name)
        || rec.num_parameters() as usize != p
        || rec.num_indices() as usize != q
        || rec.num_motives() != 1
        || rec.num_minors() as usize != n
        || rec.rules().len() != n
        || rec.k() != k_target
    {
        return Err(recursor_error(&rec_name));
    }
    let (binders, _) = peel_binders_at(rec_decl.type_(), rec_decl.type_().root(), p + n + q + 2)
        .ok_or_else(|| recursor_error(&rec_name))?;
    let styles: Vec<_> = binders.iter().map(|b| b.1).collect();
    let shape = Shape {
        name,
        levels,
        parameters,
        indices,
        constructors,
        motive_universe: if large_elimination {
            Some(&rec_levels[0])
        } else {
            None
        },
    };
    let expected = shape.recursor_type(audit, &styles)?;
    if !audit.equal(rec_decl.type_(), &expected)? {
        return Err(recursor_error(&rec_name));
    }
    declared_type_is_a_type(&staged, &rec_name, rec_decl, &audit.budget, audit.cancelled)
        .map_err(|v| map_member_preamble(&rec_name, v))?;
    for (index, rule) in rec.rules().iter().enumerate() {
        audit.tick()?;
        let ctor = &shape.constructors[index];
        if rule.constructor() != ctor.entry.name()
            || rule.num_fields() as usize != ctor.fields.len()
        {
            return Err(recursor_error(&rec_name));
        }
        let expected = shape.rule(audit, index, &rec_name)?;
        if !audit.equal(rule.rhs(), &expected)? {
            return Err(recursor_error(&rec_name));
        }
    }
    stage_inductive_member(&staged, rec_entry, environment_budget, audit.cancelled)?;
    let mut members = vec![name.clone()];
    members.extend(shape.constructors.iter().map(|c| c.entry.name().clone()));
    members.push(rec_name);
    Ok(members)
}
