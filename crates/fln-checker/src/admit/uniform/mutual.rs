//! Independent reconstruction of a bounded, safe mutual data-inductive block.
//!
//! All type headers are checked against the predecessor before any are staged.
//! Constructor telescopes determine the ordered motives, minors and recursive
//! calls. Decoded recursor types and rules are comparison subjects, never the
//! source of their expected types. No primary-kernel implementation is used.
//! Nested recursion and proposition-valued mutual families remain nonanswers.
use super::*;
use crate::whnf::{WhnfContext, WhnfOutcome, whnf_core_at_with};

struct Family<'a> {
    entry: &'a ConstantEntry,
    indices: Vec<Binder>,
    minors: std::ops::Range<usize>,
}
struct Child {
    family: usize,
    recursive: RecursiveField,
}
struct Minor<'a> {
    entry: &'a ConstantEntry,
    family: usize,
    fields: Vec<Binder>,
    children: Vec<Child>,
    result_indices: Vec<WireExpr>,
}
struct Block<'a> {
    names: Vec<WireName>,
    levels: Vec<WireName>,
    parameters: Vec<Binder>,
    families: Vec<Family<'a>>,
    minors: Vec<Minor<'a>>,
    motive_universe: WireName,
}

fn mentions_any(
    audit: &mut Audit<'_>,
    term: &WireExpr,
    root: ExprId,
    names: &[WireName],
) -> Result<bool, InductiveVerdict> {
    for name in names {
        audit.tick()?;
        let field = ConstructorField {
            source: term,
            name,
            style: BinderStyle::Default,
            type_root: root,
        };
        if field_mentions_inductive(&field, name, audit.comparison, audit.cancelled)? {
            return Ok(true);
        }
    }
    Ok(false)
}

impl Block<'_> {
    fn child(
        &self,
        audit: &mut Audit<'_>,
        term: &WireExpr,
        field: usize,
    ) -> Result<Option<Child>, InductiveVerdict> {
        // Every function domain must avoid EVERY family in the block. Checking
        // just the codomain's family would miss a negative cross-family cycle.
        let mut tail = term.root();
        loop {
            audit.tick()?;
            match term.node(tail) {
                Some(ExprNode::Metadata { expression, .. }) => tail = *expression,
                Some(ExprNode::Forall {
                    binder_type, body, ..
                }) => {
                    if mentions_any(audit, term, *binder_type, &self.names)? {
                        return Err(constructor_error(&self.names[0]));
                    }
                    tail = *body;
                }
                _ => break,
            }
        }
        for (family, info) in self.families.iter().enumerate() {
            audit.tick()?;
            if let Some(recursive) = audit.recursive_field(
                term,
                info.entry.name(),
                &self.levels,
                self.parameters.len(),
                field,
                info.indices.len(),
            )? {
                for index in &recursive.indices {
                    if mentions_any(audit, index, index.root(), &self.names)? {
                        return Err(constructor_error(info.entry.name()));
                    }
                }
                return Ok(Some(Child { family, recursive }));
            }
        }
        if mentions_any(audit, term, term.root(), &self.names)? {
            // The pin tests a field after whnf (`is_rec_argument`). A head redex
            // is recursive there: a nested family's `RBNode` field becomes
            // `(fun _ => Json) k` once its lambda parameter is instantiated.
            if let Some(reduced) = reduced_codomain(audit, term)? {
                return self.child(audit, &reduced, field);
            }
            return Err(InductiveVerdict::Deferred(InductiveSupportLimit::Recursive));
        }
        Ok(None)
    }

    fn motive(
        &self,
        audit: &mut Audit<'_>,
        builder: &mut StructuralTermBuilder,
        family: usize,
    ) -> Result<ExprId, InductiveVerdict> {
        let info = &self.families[family];
        let q = info.indices.len();
        // Earlier motives sit between the parameters and this motive's indices.
        let mut domain = application(
            builder,
            info.entry.name(),
            &self.levels,
            self.parameters.len(),
            family + q,
        );
        for index in 0..q {
            let value = builder.bvar((q - index - 1) as u32);
            domain = builder.apply(domain, value);
        }
        let sort = builder.sort_parameter(&self.motive_universe);
        let mut body = builder.forall("major", BinderStyle::Default, domain, sort);
        for (index, binder) in info.indices.iter().enumerate().rev() {
            let domain = audit.shifted(builder, &binder.domain, family, index)?;
            body = builder.forall_name(&binder.name, binder.style, domain, body);
        }
        Ok(body)
    }

    fn minor(
        &self,
        audit: &mut Audit<'_>,
        builder: &mut StructuralTermBuilder,
        index: usize,
    ) -> Result<ExprId, InductiveVerdict> {
        let ctor = &self.minors[index];
        let m = self.families.len();
        let f = ctor.fields.len();
        let r = ctor.children.len();
        let prefix = m + index;
        let mut constructed = application(
            builder,
            ctor.entry.name(),
            &self.levels,
            self.parameters.len(),
            prefix + f + r,
        );
        for field in 0..f {
            let value = builder.bvar((f + r - field - 1) as u32);
            constructed = builder.apply(constructed, value);
        }
        let mut motive = builder.bvar((prefix + f + r - ctor.family - 1) as u32);
        for result in &ctor.result_indices {
            let value = audit.relocated(builder, result, f, prefix, r)?;
            motive = builder.apply(motive, value);
        }
        let mut body = builder.apply(motive, constructed);
        for (ih, child) in ctor.children.iter().enumerate().rev() {
            let recursive = &child.recursive;
            let field = recursive.field;
            let arity = recursive.arguments.len();
            let mut motive = builder.bvar((prefix + f + ih + arity - child.family - 1) as u32);
            for index in &recursive.indices {
                let value =
                    audit.relocated_under(builder, index, field, prefix, f - field + ih, arity)?;
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
                    prefix,
                    f - field + ih,
                    position,
                )?;
                domain = builder.forall_name(&argument.name, argument.style, ty, domain);
            }
            body = builder.forall("ih", BinderStyle::Default, domain, body);
        }
        for (field, binder) in ctor.fields.iter().enumerate().rev() {
            let domain = audit.shifted(builder, &binder.domain, prefix, field)?;
            body = builder.forall_name(&binder.name, binder.style, domain, body);
        }
        Ok(body)
    }

    fn recursor_type(
        &self,
        audit: &mut Audit<'_>,
        family: usize,
        styles: &[BinderStyle],
    ) -> Result<WireExpr, InductiveVerdict> {
        let mut builder = StructuralTermBuilder::new();
        let m = self.families.len();
        let n = self.minors.len();
        let p = self.parameters.len();
        let info = &self.families[family];
        let q = info.indices.len();
        let mut motive = builder.bvar((m + n + q - family) as u32);
        for index in 0..q {
            let value = builder.bvar((q - index) as u32);
            motive = builder.apply(motive, value);
        }
        let major = builder.bvar(0);
        let result = builder.apply(motive, major);
        let mut domain = application(&mut builder, info.entry.name(), &self.levels, p, m + n + q);
        for index in 0..q {
            let value = builder.bvar((q - index - 1) as u32);
            domain = builder.apply(domain, value);
        }
        let mut body = builder.forall("major", styles[p + m + n + q], domain, result);
        for (index, binder) in info.indices.iter().enumerate().rev() {
            let domain = audit.shifted(&mut builder, &binder.domain, m + n, index)?;
            body = builder.forall_name(&binder.name, styles[p + m + n + index], domain, body);
        }
        for index in (0..n).rev() {
            let domain = self.minor(audit, &mut builder, index)?;
            body = builder.forall("minor", styles[p + m + index], domain, body);
        }
        for index in (0..m).rev() {
            let domain = self.motive(audit, &mut builder, index)?;
            body = builder.forall("motive", styles[p + index], domain, body);
        }
        for (index, parameter) in self.parameters.iter().enumerate().rev() {
            let domain = audit.import(&mut builder, &parameter.domain)?;
            body = builder.forall_name(&parameter.name, styles[index], domain, body);
        }
        audit.finish(builder, body)
    }

    fn rule(&self, audit: &mut Audit<'_>, index: usize) -> Result<WireExpr, InductiveVerdict> {
        let mut builder = StructuralTermBuilder::new();
        let ctor = &self.minors[index];
        let m = self.families.len();
        let n = self.minors.len();
        let f = ctor.fields.len();
        let prefix = m + n;
        let mut body = builder.bvar((f + n - index - 1) as u32);
        for field in 0..f {
            let value = builder.bvar((f - field - 1) as u32);
            body = builder.apply(body, value);
        }
        let mut levels = vec![self.motive_universe.clone()];
        levels.extend_from_slice(&self.levels);
        for child in &ctor.children {
            let recursive = &child.recursive;
            let field = recursive.field;
            let arity = recursive.arguments.len();
            let recursor = checker_child(&self.names[child.family], "rec");
            let mut call = application(
                &mut builder,
                &recursor,
                &levels,
                self.parameters.len(),
                prefix + f + arity,
            );
            for motive in 0..m {
                let value = builder.bvar((prefix + f + arity - motive - 1) as u32);
                call = builder.apply(call, value);
            }
            for minor in 0..n {
                let value = builder.bvar((n + f + arity - minor - 1) as u32);
                call = builder.apply(call, value);
            }
            for index in &recursive.indices {
                let value =
                    audit.relocated_under(&mut builder, index, field, prefix, f - field, arity)?;
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
                    prefix,
                    f - field,
                    position,
                )?;
                call = builder.lambda_name(&argument.name, argument.style, domain, call);
            }
            body = builder.apply(body, call);
        }
        for (field, binder) in ctor.fields.iter().enumerate().rev() {
            let domain = audit.shifted(&mut builder, &binder.domain, prefix, field)?;
            body = builder.lambda_name(&binder.name, binder.style, domain, body);
        }
        for index in (0..n).rev() {
            let domain = self.minor(audit, &mut builder, index)?;
            body = builder.lambda("minor", BinderStyle::Default, domain, body);
        }
        for index in (0..m).rev() {
            let domain = self.motive(audit, &mut builder, index)?;
            body = builder.lambda("motive", BinderStyle::Default, domain, body);
        }
        for parameter in self.parameters.iter().rev() {
            let domain = audit.import(&mut builder, &parameter.domain)?;
            body = builder.lambda_name(&parameter.name, parameter.style, domain, body);
        }
        audit.finish(builder, body)
    }
}

/// `term`'s telescope with its codomain in weak head normal form (no delta), or
/// `None` when nothing reduces or the reduction does not complete. The binders
/// are kept as written, as the pin keeps a recursive field's own type and reads
/// only the reduced form.
fn reduced_codomain(
    audit: &mut Audit<'_>,
    term: &WireExpr,
) -> Result<Option<WireExpr>, InductiveVerdict> {
    let mut binders = Vec::new();
    let mut tail = term.root();
    loop {
        audit.tick()?;
        match term.node(tail) {
            Some(ExprNode::Metadata { expression, .. }) => tail = *expression,
            Some(ExprNode::Forall {
                binder_name,
                binder_type,
                body,
                style,
            }) => {
                binders.push(Binder {
                    name: binder_name.clone(),
                    style: *style,
                    domain: audit.piece(term, *binder_type)?,
                });
                tail = *body;
            }
            _ => break,
        }
    }
    let budget = audit.budget.inference.whnf;
    let WhnfOutcome::Complete(result) = whnf_core_at_with(
        term,
        tail,
        &WhnfContext::default(),
        budget,
        &mut *audit.cancelled,
    ) else {
        return Ok(None);
    };
    if result.reductions == 0 {
        return Ok(None);
    }
    let mut builder = StructuralTermBuilder::new();
    let mut root = audit.import(&mut builder, &result.term)?;
    for binder in binders.iter().rev() {
        let domain = audit.import(&mut builder, &binder.domain)?;
        root = builder.forall_name(&binder.name, binder.style, domain, root);
    }
    audit.finish(builder, root).map(Some)
}

pub(in crate::admit) fn admit(
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

fn field_limit(observed: usize) -> InductiveVerdict {
    InductiveVerdict::Deferred(InductiveSupportLimit::FieldCount {
        observed,
        limit: MAX_NONRECURSIVE_FIELDS,
    })
}

#[allow(clippy::too_many_lines)]
pub(super) fn check(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    first: &ConstantEntry,
    environment_budget: EnvironmentBudget,
    audit: &mut Audit<'_>,
) -> Result<Vec<WireName>, InductiveVerdict> {
    audit.tick()?;
    let header = first.declaration();
    let metadata = header
        .inductive_metadata()
        .ok_or_else(|| constructor_error(first.name()))?;
    let names = metadata.mutual();
    if names.len() < 2 || names.len() > MAX_MUTUAL_TYPES {
        return Err(InductiveVerdict::Deferred(
            InductiveSupportLimit::MultipleTypes {
                observed: names.len(),
            },
        ));
    }
    if names.iter().collect::<BTreeSet<_>>().len() != names.len() {
        return Err(constructor_error(first.name()));
    }
    let levels = header.level_parameters();
    if levels.len() > 8 {
        return Err(InductiveVerdict::Deferred(
            InductiveSupportLimit::UniverseParameters {
                observed: levels.len(),
            },
        ));
    }
    if levels.iter().collect::<BTreeSet<_>>().len() != levels.len() {
        return Err(constructor_error(first.name()));
    }
    let p = metadata.num_parameters() as usize;
    if p > MAX_NONRECURSIVE_FIELDS {
        return Err(field_limit(p));
    }
    // Size and identity checks precede reconstruction, including untrusted rule
    // tables. The outer entry point has independently bounded the row count.
    let mut seen = BTreeSet::new();
    let mut units = 0usize;
    for entry in declarations {
        audit.tick()?;
        if !seen.insert(entry.name()) || environment.find(entry.name()).is_some() {
            return Err(InductiveVerdict::Rejected(
                InductiveRejection::NameAlreadyDeclared {
                    name: entry.name().clone(),
                },
            ));
        }
        units = units.saturating_add(size(entry.declaration().type_()));
        if let Some(rec) = entry.declaration().recursor_metadata() {
            if rec.rules().len() > MAX_NONRECURSIVE_CONSTRUCTORS {
                return Err(recursor_error(entry.name()));
            }
            for rule in rec.rules() {
                audit.tick()?;
                units = units.saturating_add(size(rule.rhs()));
                if units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
                    return Err(arena_limit(units));
                }
            }
        }
        if units > MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
            return Err(arena_limit(units));
        }
    }
    let mut block = Block {
        names: names.to_vec(),
        levels: levels.to_vec(),
        parameters: Vec::new(),
        families: Vec::new(),
        minors: Vec::new(),
        motive_universe: checker_atom("_unused_mutual_universe"),
    };
    let mut result_sort = None;
    let mut n = 0usize;
    let mut binders = p;
    for name in &block.names {
        audit.tick()?;
        let entry = declarations
            .iter()
            .find(|e| e.name() == name)
            .ok_or_else(|| constructor_error(name))?;
        let declaration = entry.declaration();
        let metadata = declaration
            .inductive_metadata()
            .ok_or_else(|| constructor_error(name))?;
        if declaration.safety() != ConstantSafety::Safe {
            return Err(InductiveVerdict::Deferred(InductiveSupportLimit::Unsafe));
        }
        if metadata.num_nested() != 0 {
            return Err(InductiveVerdict::Deferred(InductiveSupportLimit::Nested {
                observed: metadata.num_nested(),
            }));
        }
        if declaration.level_parameters() != block.levels
            || metadata.mutual() != block.names
            || metadata.num_parameters() as usize != p
        {
            return Err(constructor_error(name));
        }
        let q = metadata.num_indices() as usize;
        binders = binders.saturating_add(q);
        if binders > MAX_NONRECURSIVE_FIELDS {
            return Err(field_limit(binders));
        }
        if !positive_result(declaration, (p + q) as u32) {
            return Err(InductiveVerdict::Deferred(
                InductiveSupportLimit::ResultUniverse,
            ));
        }
        // NO sibling is visible here. Otherwise a cyclic signature could use
        // the staging environment to justify itself before constructor checking.
        declared_type_is_a_type(
            environment,
            name,
            declaration,
            &audit.budget,
            audit.cancelled,
        )
        .map_err(|v| map_member_preamble(name, v))?;
        let (parameters, tail) = audit.peel(declaration.type_(), p)?;
        let (indices, sort) = audit.peel(&tail, q)?;
        if let Some(expected) = &result_sort {
            if !audit.equal(&sort, expected)? {
                return Err(constructor_error(name));
            }
            for (actual, expected) in parameters.iter().zip(&block.parameters) {
                if !audit.equal(&actual.domain, &expected.domain)? {
                    return Err(constructor_error(name));
                }
            }
        } else {
            result_sort = Some(sort);
            block.parameters = parameters;
        }
        let start = n;
        n = n.saturating_add(metadata.constructors().len());
        if n > MAX_NONRECURSIVE_CONSTRUCTORS {
            return Err(InductiveVerdict::Deferred(
                InductiveSupportLimit::ConstructorCount {
                    observed: n,
                    limit: MAX_NONRECURSIVE_CONSTRUCTORS,
                },
            ));
        }
        block.families.push(Family {
            entry,
            indices,
            minors: start..n,
        });
    }
    let expected = n + 2 * block.families.len();
    if declarations.len() != expected {
        return Err(InductiveVerdict::Rejected(
            InductiveRejection::DeclarationCount {
                observed: declarations.len(),
                expected,
            },
        ));
    }
    let sort = result_sort.ok_or_else(overflow)?;
    let Some(ExprNode::Sort { level }) = sort.node(sort.root()) else {
        return Err(overflow());
    };
    let result_level = WireLevel::from_parts(sort.levels().to_vec(), *level);
    let mut staged = environment.clone();
    for family in &block.families {
        staged =
            stage_inductive_member(&staged, family.entry, environment_budget, audit.cancelled)?;
    }
    let mut locals = Vec::new();
    for parameter in &block.parameters {
        audit.append_local(&mut locals, &parameter.domain)?;
    }
    let mut constructor_names = BTreeSet::new();
    let mut total_fields = 0usize;
    for family in 0..block.families.len() {
        let info = &block.families[family];
        let metadata = info
            .entry
            .declaration()
            .inductive_metadata()
            .ok_or_else(overflow)?;
        for (index, name) in metadata.constructors().iter().enumerate() {
            audit.tick()?;
            if !constructor_names.insert(name) {
                return Err(InductiveVerdict::Rejected(
                    InductiveRejection::RepeatedConstructor { name: name.clone() },
                ));
            }
            let entry = declarations
                .iter()
                .find(|e| e.name() == name)
                .ok_or_else(|| {
                    InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                        name: name.clone(),
                    })
                })?;
            let declaration = entry.declaration();
            let cm = declaration
                .constructor_metadata()
                .ok_or_else(|| constructor_error(name))?;
            let f = cm.num_fields() as usize;
            total_fields = total_fields.saturating_add(f);
            if total_fields > MAX_NONRECURSIVE_FIELDS {
                return Err(field_limit(total_fields));
            }
            if declaration.safety() != ConstantSafety::Safe
                || declaration.level_parameters() != block.levels
                || cm.inductive() != info.entry.name()
                || cm.index() as usize != index
                || cm.num_parameters() as usize != p
            {
                return Err(constructor_error(name));
            }
            declared_type_is_a_type(&staged, name, declaration, &audit.budget, audit.cancelled)
                .map_err(|v| map_member_preamble(name, v))?;
            let (parameters, tail) = audit.peel(declaration.type_(), p)?;
            for (actual, expected) in parameters.iter().zip(&block.parameters) {
                if !audit.equal(&actual.domain, &expected.domain)? {
                    return Err(constructor_error(name));
                }
            }
            if peel_binders_at(&tail, tail.root(), f).is_none() {
                return Err(constructor_error(name));
            }
            let (fields, result) = audit.peel(&tail, f)?;
            let result_indices = audit
                .family_indices(
                    &result,
                    info.entry.name(),
                    &block.levels,
                    p,
                    f,
                    info.indices.len(),
                )?
                .ok_or_else(|| constructor_error(name))?;
            for index in &result_indices {
                if mentions_any(audit, index, index.root(), &block.names)? {
                    return Err(constructor_error(name));
                }
            }
            let mut field_locals = locals.clone();
            let mut children = Vec::new();
            for (field_index, field) in fields.iter().enumerate() {
                if let Some(child) = block.child(audit, &field.domain, field_index)? {
                    children.push(child);
                }
                let open = audit.open(&field.domain, &field_locals)?;
                let context = InferenceContext::new(
                    field_locals.clone(),
                    block.levels.clone(),
                    staged.clone(),
                )
                .map_err(|_| overflow())?;
                let facts = type_is_type_in_context(
                    name,
                    &open,
                    &context,
                    ConstantSafety::Safe,
                    &audit.budget,
                    audit.cancelled,
                )
                .map_err(|v| map_member_preamble(name, v))?;
                if !universe_within(&facts.universe, &result_level, audit)? {
                    if facts.explicit_universe.is_some()
                        && normalize(&result_level)
                            .ok()
                            .and_then(|n| explicit_normal_universe(&n))
                            .is_some()
                    {
                        return Err(constructor_error(name));
                    }
                    return Err(InductiveVerdict::Deferred(
                        InductiveSupportLimit::ResultUniverse,
                    ));
                }
                audit.append_local(&mut field_locals, &field.domain)?;
            }
            staged = stage_inductive_member(&staged, entry, environment_budget, audit.cancelled)?;
            block.minors.push(Minor {
                entry,
                family,
                fields,
                children,
                result_indices,
            });
        }
    }
    let recursive = block.minors.iter().any(|c| !c.children.is_empty());
    let reflexive = block
        .minors
        .iter()
        .flat_map(|c| &c.children)
        .any(|c| !c.recursive.arguments.is_empty());
    for family in &block.families {
        let metadata = family
            .entry
            .declaration()
            .inductive_metadata()
            .ok_or_else(overflow)?;
        if metadata.is_recursive() != recursive || metadata.is_reflexive() != reflexive {
            return Err(constructor_error(family.entry.name()));
        }
    }
    // Annotation erasure affects ONLY regenerated eliminator binders. Original
    // annotated constructor signatures above were fully checked and retained.
    audit.recursor_binders(&mut block.parameters)?;
    for family in &mut block.families {
        audit.recursor_binders(&mut family.indices)?;
    }
    for minor in &mut block.minors {
        audit.recursor_binders(&mut minor.fields)?;
        for child in &mut minor.children {
            audit.recursor_binders(&mut child.recursive.arguments)?;
        }
    }
    let mut recursors = Vec::new();
    for family in 0..block.families.len() {
        audit.tick()?;
        let info = &block.families[family];
        let name = checker_child(info.entry.name(), "rec");
        let entry = declarations
            .iter()
            .find(|e| e.name() == &name)
            .ok_or_else(|| {
                InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
                    name: name.clone(),
                })
            })?;
        let declaration = entry.declaration();
        let rec = declaration
            .recursor_metadata()
            .ok_or_else(|| recursor_error(&name))?;
        let levels = declaration.level_parameters();
        if declaration.safety() != ConstantSafety::Safe
            || levels.len() != block.levels.len() + 1
            || levels[1..] != block.levels
            || block.levels.contains(&levels[0])
            || rec.mutual() != block.names
            || rec.num_parameters() as usize != p
            || rec.num_indices() as usize != info.indices.len()
            || rec.num_motives() as usize != block.families.len()
            || rec.num_minors() as usize != n
            || rec.rules().len() != info.minors.len()
            || rec.k()
        {
            return Err(recursor_error(&name));
        }
        if family == 0 {
            block.motive_universe = levels[0].clone();
        } else if block.motive_universe != levels[0] {
            return Err(recursor_error(&name));
        }
        let count = p + block.families.len() + n + info.indices.len() + 1;
        let (binders, _) = peel_binders_at(declaration.type_(), declaration.type_().root(), count)
            .ok_or_else(|| recursor_error(&name))?;
        let styles: Vec<_> = binders.iter().map(|b| b.1).collect();
        let expected = block.recursor_type(audit, family, &styles)?;
        if !audit.equal(declaration.type_(), &expected)? {
            return Err(recursor_error(&name));
        }
        declared_type_is_a_type(&staged, &name, declaration, &audit.budget, audit.cancelled)
            .map_err(|v| map_member_preamble(&name, v))?;
        for (index, rule) in info.minors.clone().zip(rec.rules()) {
            audit.tick()?;
            let ctor = &block.minors[index];
            if rule.constructor() != ctor.entry.name()
                || rule.num_fields() as usize != ctor.fields.len()
            {
                return Err(recursor_error(&name));
            }
            let expected = block.rule(audit, index)?;
            if !audit.equal(rule.rhs(), &expected)? {
                return Err(recursor_error(&name));
            }
        }
        recursors.push(entry);
    }
    // Staging is private to this check. An omitted/malformed later recursor,
    // allocation stop, or final cancellation cannot return a partial admission.
    for entry in &recursors {
        staged = stage_inductive_member(&staged, entry, environment_budget, audit.cancelled)?;
    }
    audit.tick()?;
    let mut members = block.names.clone();
    members.extend(block.minors.iter().map(|c| c.entry.name().clone()));
    members.extend(recursors.into_iter().map(|e| e.name().clone()));
    Ok(members)
}
