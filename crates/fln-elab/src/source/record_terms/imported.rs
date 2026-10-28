//! Imported flat record constructors and dependency-ordered field defaults.
//!
//! Structure metadata identifies fields and parents, while ordinary admitted
//! definitions supply the flat constructor and each default body. This mirrors
//! the pin's StructInst and instantiateStructDefaultValueFn? paths without
//! extending the separate SourceRecordDefaults constructor-prefix contract.
use super::*;
use crate::records::imported::{ImportedStructures, StructureEntry};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

#[derive(Clone)]
struct Projection {
    owner: Name,
    name: Name,
    index: Option<u32>,
}

#[derive(Clone)]
struct Leaf {
    name: Name,
    style: BinderInfo,
    path: Vec<Projection>,
}

#[derive(Clone)]
struct Parent {
    name: Name,
    path: Vec<Projection>,
    leaves: Vec<Leaf>,
}

pub(super) struct ImportedLayout {
    structures: ImportedStructures,
    root: Name,
    leaves: Vec<Leaf>,
    parents: Vec<Parent>,
}

enum Input<'a> {
    Explicit(&'a Syntax),
    Copy(Typed),
    Missing,
}

struct Field<'a> {
    name: Name,
    type_: Expr,
    hole: Expr,
    style: BinderInfo,
    input: Input<'a>,
    // Parent dictionary inference must not fill a field explicitly supplied by
    // syntax or by an update source, even after another parent has been tried.
    allowed_parent: bool,
    instance: bool,
}

pub(super) struct ImportedRecord<'a> {
    frame: RecordFrame<'a>,
    layout: ImportedLayout,
    fields: Vec<Field<'a>>,
    cursor: usize,
    defaults_done: bool,
}

struct DefaultValue {
    dependencies: BTreeSet<Name>,
    value: Typed,
}

struct Pending {
    index: usize,
    value: Option<DefaultValue>,
}

fn malformed() -> NatDefinitionElabError {
    error(RecordTermError::ExpectedRecordType)
}

fn limit() -> NatDefinitionElabError {
    failure(SourceInferenceError::ResourceLimit)
}

impl Context {
    pub(super) fn imported_record_layout(
        &mut self,
        frame: &RecordFrame<'_>,
    ) -> Result<Option<ImportedLayout>, NatDefinitionElabError> {
        self.tick()?;
        let mut head = &frame.constructor.value;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(malformed());
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(name) else {
            return Err(malformed());
        };
        let root = ctor.induct.clone();
        let structures = ImportedStructures::read(&self.txn.env)
            .map_err(|problem| failure(SourceInferenceError::Record(problem)))?;
        if structures.get(&root).is_none() {
            return Ok(None);
        }
        // Preserve the physical path for older native records. A newly frozen
        // inherited helper opts into flat dependency ordering; native declared
        // defaults in that record are adapted by their checked prefix length.
        let defaults = crate::records::defaults::RecordDefaults::read(&self.txn.env)
            .map_err(|problem| failure(SourceInferenceError::Record(problem)))?;
        let mut native = false;
        let mut pending = vec![root.clone()];
        let mut seen = BTreeSet::new();
        while let Some(record) = pending.pop() {
            self.tick()?;
            if !seen.insert(record.clone()) {
                continue;
            }
            if seen.len() > RecordBudget::default().max_binders {
                return Err(limit());
            }
            // Native seed parents can have only a physical constructor journal.
            // Their existing source path remains usable; artifact export separately
            // requires complete interfaces for every owned record's parents.
            let Some(row) = structures.get(&record) else {
                return Ok(None);
            };
            for index in 0..row.fields.len() {
                self.tick()?;
                let index = u32::try_from(index).map_err(|_| limit())?;
                if defaults.helper(&record, index).is_some() {
                    native = true;
                }
            }
            for parent in row.parents.iter().map(|parent| &parent.name).chain(
                row.fields
                    .iter()
                    .filter_map(|field| field.subobject.as_ref()),
            ) {
                self.tick()?;
                pending.push(parent.clone());
            }
        }
        let order = self.imported_parent_order(&structures, &root, None)?;
        let leaves = self.imported_record_leaves(&structures, &root)?;
        if native
            && !leaves.iter().any(|field| {
                self.txn.env.contains(&Name::str(
                    root.append_core(&field.name),
                    "_inherited_default",
                ))
            })
        {
            return Ok(None);
        }
        // Whole-parent syntax keeps the existing physical constructor path.
        // In particular, it keeps its checked once-only source bindings and
        // does not decompose a parent value whose dependent fields may matter.
        if frame
            .fields
            .keys()
            .any(|name| !leaves.iter().any(|leaf| &leaf.name == name))
        {
            return Ok(None);
        }
        let mut parents = Vec::new();
        for name in order.into_iter().skip(1) {
            self.tick()?;
            let path = self.imported_parent_path(&structures, &root, &name)?;
            let parent_leaves = self.imported_record_leaves(&structures, &name)?;
            if parent_leaves
                .iter()
                .any(|leaf| !leaves.iter().any(|target| target.name == leaf.name))
            {
                return Err(malformed());
            }
            parents.push(Parent {
                name,
                path,
                leaves: parent_leaves,
            });
        }
        Ok(Some(ImportedLayout {
            structures,
            root,
            leaves,
            parents,
        }))
    }

    pub(super) fn start_imported_record<'a>(
        &mut self,
        mut frame: RecordFrame<'a>,
        layout: ImportedLayout,
    ) -> Result<ImportedRecord<'a>, NatDefinitionElabError> {
        let mut parameters = Vec::new();
        let mut head = &frame.constructor.value;
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            parameters.push(a.clone());
            head = f;
        }
        parameters.reverse();
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(malformed());
        };
        let flat_name = Name::str(name.clone(), "_flat_ctor");
        let Some(ConstantInfo::Defn(flat)) = self.txn.env.find(&flat_name).cloned() else {
            return Err(malformed());
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(&layout.root) else {
            return Err(malformed());
        };
        if flat.safety != DefinitionSafety::Safe
            || flat.base.level_params != family.base.level_params
            || parameters.len() != family.num_params as usize
        {
            return Err(malformed());
        }
        let mut constructor = Typed {
            value: self.instantiate_params(&flat.value, &flat.base.level_params, &frame.levels)?,
            type_: self.instantiate_params(
                &flat.base.type_,
                &flat.base.level_params,
                &frame.levels,
            )?,
        };
        for parameter in &parameters {
            self.apply_imported_record_body(&mut constructor, parameter)?;
        }

        let mut fields = Vec::new();
        for leaf in &layout.leaves {
            self.tick()?;
            let type_ = self.whnf(&constructor.type_)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                binder_info,
                ..
            } = type_.node()
            else {
                return Err(malformed());
            };
            if binder_name != &leaf.name || binder_info != &leaf.style {
                return Err(malformed());
            }
            let domain = binder_type.clone();
            let hole = self.hole(domain.clone())?;
            self.apply_imported_record_body(&mut constructor, &hole)?;
            let mut input = frame.fields.remove(&leaf.name).map(Input::Explicit);
            if input.is_none() {
                for source in &frame.sources {
                    self.tick()?;
                    match self.record_field(source.clone(), &leaf.name) {
                        Ok(value) => {
                            input = Some(Input::Copy(value));
                            break;
                        }
                        Err(NatDefinitionElabError::Inference(
                            SourceInferenceError::RecordTerm(RecordTermError::UnknownField(_)),
                        )) => {}
                        Err(problem) => return Err(problem),
                    }
                }
            }
            let input = input.unwrap_or(Input::Missing);
            let allowed_parent = matches!(input, Input::Missing);
            fields.push(Field {
                name: leaf.name.clone(),
                type_: domain,
                hole,
                style: leaf.style,
                input,
                allowed_parent,
                instance: false,
            });
        }
        if !frame.fields.is_empty() {
            return Err(malformed());
        }
        self.constrain(&constructor.type_, &frame.expected)?;
        frame.constructor = constructor;
        let mut state = ImportedRecord {
            frame,
            layout,
            fields,
            cursor: 0,
            defaults_done: false,
        };
        self.infer_imported_parent_fields(&mut state)?;
        Ok(state)
    }

    /// The pin instantiates the body's lambda prefix, rather than emitting a
    /// call to a helper whose runtime attributes could select another body.
    fn apply_imported_record_body(
        &mut self,
        function: &mut Typed,
        argument: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        let type_ = self.whnf(&function.type_)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            return Err(malformed());
        };
        let ExprNode::Lam {
            binder_type: value_domain,
            body: value_body,
            ..
        } = function.value.node()
        else {
            return Err(malformed());
        };
        let argument_type = self.known_type(argument)?.ok_or_else(malformed)?;
        self.constrain(&argument_type, binder_type)?;
        self.constrain(value_domain, binder_type)?;
        function.value = self.substitute(value_body, argument)?;
        function.type_ = self.substitute(body, argument)?;
        Ok(())
    }

    pub(super) fn next_imported_record_field<'a>(
        &mut self,
        state: &mut ImportedRecord<'a>,
    ) -> Result<RecordStep<'a>, NatDefinitionElabError> {
        while state.cursor < state.fields.len() {
            self.tick()?;
            let index = state.cursor;
            let field = &mut state.fields[index];
            match &field.input {
                Input::Explicit(syntax) => {
                    return Ok(RecordStep::Field {
                        syntax,
                        domain: self.instantiate(&field.type_)?,
                        target: RecordTarget::Imported(index),
                    });
                }
                Input::Copy(value) => {
                    return Ok(RecordStep::Copy {
                        value: self.finish_explicit_term(value.clone(), Some(&field.type_))?,
                        target: RecordTarget::Imported(index),
                    });
                }
                Input::Missing => {
                    if field.style == BinderInfo::InstImplicit {
                        let instance = self.instance_hole(field.type_.clone())?;
                        self.constrain(&field.hole, &instance)?;
                        field.instance = true;
                    }
                    state.cursor += 1;
                }
            }
        }
        if !state.defaults_done {
            // StructInst synthesizes default instances before field defaults.
            // Return to the source worklist after each selection so a newly
            // ready argument can determine another numeral's type first.
            self.resolve_instances(false)?;
            self.flush(false)?;
            if self.resolve_next_default_instance()? {
                return Ok(RecordStep::Continue);
            }
            self.synthesize_imported_record_defaults(state)?;
            state.defaults_done = true;
            // Field defaults can unblock provided arguments as well. Resume
            // them before closing the checked update-source let context.
            return Ok(RecordStep::Continue);
        }
        let mut term = self
            .finish_explicit_term(state.frame.constructor.clone(), Some(&state.frame.expected))?;
        term.value = self.instantiate(&term.value)?;
        term.type_ = self.instantiate(&term.type_)?;
        for local in state.frame.source_bindings.iter().rev() {
            self.tick()?;
            let type_ = self.instantiate(&local.type_)?;
            let value = self.instantiate(local.value.as_ref().expect("record source is a let"))?;
            term.value = term
                .value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            term.type_ = term
                .type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            term.value = Expr::let_e(
                Name::anonymous(),
                type_.clone(),
                value.clone(),
                term.value,
                false,
            );
            term.type_ = Expr::let_e(Name::anonymous(), type_, value, term.type_, false);
        }
        self.txn.lctx = state.frame.saved_lctx.clone();
        Ok(RecordStep::Complete(term))
    }

    pub(super) fn accept_imported_record_field(
        &mut self,
        state: &mut ImportedRecord<'_>,
        index: usize,
        value: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        if index != state.cursor {
            return Err(failure(SourceInferenceError::Scope));
        }
        let field = state.fields.get(index).ok_or_else(malformed)?;
        self.constrain(&value.type_, &field.type_)?;
        if let ExprNode::MVar { id } = field.hole.node()
            && !self.txn.mvars.is_assigned(id)
        {
            // The supplied term is already checked against this field's type.
            // Assign it verbatim: defeq may zeta-reduce an unused strict let
            // before assigning the hole, erasing executable initialization.
            let awakened = self
                .txn
                .assign_mvar(id.clone(), value.value, AssignmentJustification::UserGiven)
                .map_err(|error| {
                    failure(SourceInferenceError::Unification(Box::new(
                        UnificationError::Metavariable(error),
                    )))
                })?;
            assert!(awakened.is_empty(), "private source queue");
        } else {
            self.constrain(&field.hole, &value.value)?;
        }
        state.cursor += 1;
        Ok(())
    }
}

impl Context {
    /// Instantiate a declared native prefix or the pin's named flat dependencies.
    /// The receiver supplies the owner's actual universe and datatype parameters;
    /// these need not have the child's order, arity, or universe names.
    pub(in crate::source) fn instantiate_record_default(
        &mut self,
        helper: &Name,
        receiver: &Typed,
        fields: &[(Name, Expr)],
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(helper).cloned() else {
            return if self.txn.env.contains(helper) {
                Err(malformed())
            } else {
                Ok(None)
            };
        };
        let target = self.whnf(&receiver.type_)?;
        let (head, parameters) = operators::spine(&target);
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(malformed());
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(malformed());
        };
        if definition.safety != DefinitionSafety::Safe
            || definition.base.level_params != family.base.level_params
            || parameters.len() != family.num_params as usize
        {
            return Err(malformed());
        }
        let defaults = crate::records::defaults::RecordDefaults::read(&self.txn.env)
            .map_err(|problem| failure(SourceInferenceError::Record(problem)))?;
        let Some(ConstantInfo::Ctor(ctor)) = family
            .ctors
            .first()
            .and_then(|ctor| self.txn.env.find(ctor))
            .cloned()
        else {
            return Err(malformed());
        };
        let native =
            (0..ctor.num_fields).find(|index| defaults.helper(name, *index) == Some(helper));
        let mut value = Typed {
            value: self.instantiate_params(
                &definition.value,
                &definition.base.level_params,
                levels,
            )?,
            type_: self.instantiate_params(
                &definition.base.type_,
                &definition.base.level_params,
                levels,
            )?,
        };
        for parameter in parameters {
            self.apply_imported_record_body(&mut value, &parameter)?;
        }
        if let Some(prefix) = native {
            // Stop at the fixed prefix even when the field itself is a function.
            for index in 0..prefix {
                self.tick()?;
                let argument = self.reduce_record_projections(&Expr::proj(
                    name.clone(),
                    u64::from(index),
                    receiver.value.clone(),
                ))?;
                self.apply_imported_record_body(&mut value, &argument)?;
            }
        } else {
            while let ExprNode::Lam { binder_name, .. } = value.value.node() {
                self.tick()?;
                let Some((_, argument)) = fields.iter().find(|(name, _)| name == binder_name)
                else {
                    return Ok(None);
                };
                self.apply_imported_record_body(&mut value, argument)?;
            }
            // An identity application marks the end of field dependencies.
            let (head, arguments) = operators::spine(&value.value);
            if matches!(head.node(), ExprNode::Const { name, .. }
                if name == &Name::from_components(["id"]))
                && arguments.len() == 2
            {
                value.value = arguments[1].clone();
            } else if matches!(head.node(), ExprNode::Lam { body, .. }
                if matches!(body.node(), ExprNode::BVar { idx: 0 }))
                && arguments.len() == 1
            {
                value.value = arguments[0].clone();
            }
        }
        value.value = self.reduce_record_projections(&value.value)?;
        value.type_ = self.reduce_record_projections(&value.type_)?;
        Ok(Some(value))
    }

    /// Reduce only projections of explicit admitted constructors, including
    /// beneath binders. This removes spurious dependencies on the rest of a
    /// reconstructed parent without unfolding arbitrary user definitions.
    pub(in crate::source) fn reduce_record_projections(
        &mut self,
        expression: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut work = vec![(expression, false)];
        let mut done: HashMap<usize, Expr> = HashMap::new();
        while let Some((term, finish)) = work.pop() {
            self.tick()?;
            if done.contains_key(&term.allocation_identity()) {
                continue;
            }
            if !finish {
                work.push((term, true));
                match term.node() {
                    ExprNode::App { f, a } => work.extend([(f, false), (a, false)]),
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        work.extend([(binder_type, false), (body, false)]);
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        work.extend([(type_, false), (value, false), (body, false)]);
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        work.push((expr, false));
                    }
                    _ => {}
                }
                continue;
            }
            let get = |expr: &Expr| done[&expr.allocation_identity()].clone();
            let result = match term.node() {
                ExprNode::App { f, a } => Expr::app(get(f), get(a)),
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    get(binder_type),
                    get(body),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    binder_name.clone(),
                    get(binder_type),
                    get(body),
                    *binder_info,
                ),
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    non_dep,
                } => Expr::let_e(
                    decl_name.clone(),
                    get(type_),
                    get(value),
                    get(body),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), get(expr)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let receiver = get(expr);
                    let (head, arguments) = operators::spine(&receiver);
                    let selected = if let ExprNode::Const { name, .. } = head.node()
                        && let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(name)
                        && ctor.induct == *struct_name
                        && arguments.len() == (ctor.num_params as usize + ctor.num_fields as usize)
                        && *idx < u64::from(ctor.num_fields)
                    {
                        Some(arguments[ctor.num_params as usize + *idx as usize].clone())
                    } else {
                        None
                    };
                    selected.unwrap_or_else(|| Expr::proj(struct_name.clone(), *idx, receiver))
                }
                _ => term.clone(),
            };
            done.insert(term.allocation_identity(), result);
        }
        done.remove(&expression.allocation_identity())
            .ok_or_else(malformed)
    }

    pub(in crate::source) fn source_record_parent_view(
        &mut self,
        structures: &ImportedStructures,
        parents: &[(Name, Typed)],
        wanted: &Name,
    ) -> Result<Typed, NatDefinitionElabError> {
        for (name, receiver) in parents {
            self.tick()?;
            if self
                .imported_parent_order(structures, name, None)?
                .contains(wanted)
            {
                let path = self.imported_parent_path(structures, name, wanted)?;
                return self.imported_project_path(receiver.clone(), &path);
            }
        }
        Err(malformed())
    }

    pub(in crate::source) fn record_has_flat_field(
        &mut self,
        structures: &ImportedStructures,
        record: &Name,
        field: &Name,
    ) -> Result<bool, NatDefinitionElabError> {
        Ok(self
            .imported_record_leaves(structures, record)?
            .iter()
            .any(|leaf| &leaf.name == field))
    }

    fn imported_field_default(
        &mut self,
        state: &ImportedRecord<'_>,
        index: usize,
    ) -> Result<Option<DefaultValue>, NatDefinitionElabError> {
        self.tick()?;
        let field = state.fields.get(index).ok_or_else(malformed)?;
        let structure = state
            .layout
            .structures
            .get(&state.layout.root)
            .ok_or_else(malformed)?;
        // Physical fields use the recorded projection identity. A child
        // override of an inherited field is named under the child itself.
        let projection = structure
            .fields
            .iter()
            .find(|row| row.name == field.name)
            .map(|row| row.projection.clone())
            .unwrap_or_else(|| state.layout.root.append_core(&field.name));
        let direct = Name::str(projection.clone(), "_default");
        let inherited = Name::str(projection, "_inherited_default");
        let helper = if self.txn.env.contains(&direct) {
            direct
        } else if self.txn.env.contains(&inherited) {
            inherited
        } else {
            return Ok(None);
        };
        let arguments: Vec<_> = state
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.hole.clone()))
            .collect();
        let Some(mut value) =
            self.instantiate_record_default(&helper, &state.frame.constructor, &arguments)?
        else {
            return Ok(None);
        };
        let mut mentioned = self.txn.mvars.collect_mvars(&value.value);
        mentioned.extend(self.txn.mvars.collect_mvars(&value.type_));
        let mut dependencies = BTreeSet::new();
        for argument in &state.fields {
            self.tick()?;
            if let ExprNode::MVar { id } = argument.hole.node()
                && mentioned.contains(id)
            {
                dependencies.insert(argument.name.clone());
            }
        }
        let actual_type = self.known_type(&value.value)?.ok_or_else(malformed)?;
        self.constrain(&actual_type, &field.type_)?;
        value.type_ = actual_type;
        Ok(Some(DefaultValue {
            dependencies,
            value,
        }))
    }

    fn synthesize_imported_record_defaults(
        &mut self,
        state: &ImportedRecord<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        self.flush(false)?;
        self.resolve_instances(false)?;
        let mut pending = Vec::new();
        let mut names = BTreeSet::new();
        for (index, field) in state.fields.iter().enumerate() {
            self.tick()?;
            if !matches!(field.input, Input::Missing) {
                continue;
            }
            let unresolved = matches!(self.instantiate(&field.hole)?.node(), ExprNode::MVar { .. });
            if field.instance {
                if unresolved {
                    return Err(error(RecordTermError::MissingField(field.name.clone())));
                }
                continue;
            }
            // Explicit missing fields require a source/default even if a
            // dependent equation happened to infer their value.
            if field.style == BinderInfo::Default || unresolved {
                names.insert(field.name.clone());
                pending.push(Pending { index, value: None });
            }
        }
        for field in &mut pending {
            self.tick()?;
            field.value = self.imported_field_default(state, field.index)?;
        }
        while !pending.is_empty() {
            self.tick()?;
            let mut progress = false;
            let mut retained = Vec::new();
            let mut last_problem = None;
            let ready_names = names.clone();
            for field in pending {
                self.tick()?;
                let target = &state.fields[field.index];
                let ready = field.value.as_ref().is_some_and(|value| {
                    value
                        .dependencies
                        .iter()
                        .all(|name| !ready_names.contains(name))
                });
                if !ready {
                    retained.push(field);
                    continue;
                }
                let value = &field.value.as_ref().expect("ready default").value;
                let mut trial = self.clone();
                let attempt = (|| {
                    trial.constrain(&value.type_, &target.type_)?;
                    if matches!(
                        trial.instantiate(&target.hole)?.node(),
                        ExprNode::MVar { .. }
                    ) {
                        trial.constrain(&target.hole, &value.value)?;
                    }
                    trial.flush(false)?;
                    Ok::<_, NatDefinitionElabError>(!matches!(
                        trial.instantiate(&target.hole)?.node(),
                        ExprNode::MVar { .. }
                    ))
                })();
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                match attempt {
                    Ok(true) => {
                        *self = trial;
                        names.remove(&target.name);
                        progress = true;
                    }
                    Ok(false) => retained.push(field),
                    Err(problem) if instances::nonmatch(&problem) => {
                        last_problem = Some(problem);
                        retained.push(field);
                    }
                    Err(problem) => return Err(problem),
                }
            }
            if !progress {
                if let Some(problem) = last_problem {
                    return Err(problem);
                }
                let missing = &state.fields[retained.first().ok_or_else(malformed)?.index];
                return Err(error(RecordTermError::MissingField(missing.name.clone())));
            }
            pending = retained;
        }
        Ok(())
    }

    fn infer_imported_parent_fields(
        &mut self,
        state: &mut ImportedRecord<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        let registry = self.instance_registry()?;
        let mut attempted = BTreeSet::new();
        loop {
            self.tick()?;
            let mut progress = false;
            for parent in &state.layout.parents {
                self.tick()?;
                if attempted.contains(&parent.name) || !registry.is_class(&parent.name) {
                    continue;
                }
                let mut indices = Vec::new();
                for leaf in &parent.leaves {
                    self.tick()?;
                    let index = state
                        .fields
                        .iter()
                        .position(|field| field.name == leaf.name)
                        .ok_or_else(malformed)?;
                    indices.push(index);
                }
                if !indices
                    .iter()
                    .all(|index| state.fields[*index].allowed_parent)
                    || !indices
                        .iter()
                        .any(|index| matches!(state.fields[*index].input, Input::Missing))
                {
                    continue;
                }
                let receiver =
                    self.imported_project_path(state.frame.constructor.clone(), &parent.path)?;
                let domain = self.instantiate(&receiver.type_)?;
                if self.imported_unfilled_field_occurs(state, &domain)? {
                    continue;
                }
                // Optional parent search is a checked transaction. Its private
                // instance goal cannot constrain the following default search
                // unless the complete parent dictionary and all projections fit.
                let mut trial = self.clone();
                let mut retry = false;
                let attempt = (|| {
                    trial.flush(false)?;
                    let saved = trial.txn.lctx.clone();
                    let suspended = std::mem::take(&mut trial.equations);
                    let hole = trial.instance_hole(domain.clone())?;
                    let ExprNode::MVar { id } = hole.node() else {
                        return Err(malformed());
                    };
                    match trial.search_instance(id.clone(), &registry)? {
                        instances::SearchResult::Solved => {}
                        instances::SearchResult::Stuck => {
                            retry = true;
                            return Ok(None);
                        }
                        instances::SearchResult::Failed => return Ok(None),
                    }
                    trial.txn.lctx = saved;
                    trial.equations.extend(suspended);
                    let value = trial.instantiate(&hole)?;
                    if value.has_expr_mvar() || value.has_level_mvar() {
                        return Ok(None);
                    }
                    let instance = Typed {
                        value,
                        type_: domain.clone(),
                    };
                    let mut updates = Vec::new();
                    for (leaf, index) in parent.leaves.iter().zip(&indices) {
                        trial.tick()?;
                        let value = trial.imported_project_path(instance.clone(), &leaf.path)?;
                        trial.constrain(&value.type_, &state.fields[*index].type_)?;
                        trial.constrain(&state.fields[*index].hole, &value.value)?;
                        updates.push((*index, value));
                    }
                    Ok::<_, NatDefinitionElabError>(Some(updates))
                })();
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                if !retry {
                    attempted.insert(parent.name.clone());
                }
                match attempt {
                    Ok(Some(updates)) => {
                        *self = trial;
                        for (index, value) in updates {
                            if matches!(state.fields[index].input, Input::Missing) {
                                state.fields[index].input = Input::Copy(value);
                                progress = true;
                            }
                        }
                    }
                    Ok(None) => {}
                    Err(problem) if instances::nonmatch(&problem) => {}
                    Err(problem) => return Err(problem),
                }
            }
            if !progress {
                return Ok(());
            }
        }
    }

    fn imported_unfilled_field_occurs(
        &mut self,
        state: &ImportedRecord<'_>,
        expression: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut holes = HashSet::new();
        for field in &state.fields {
            self.tick()?;
            if let ExprNode::MVar { id } = self.instantiate(&field.hole)?.node() {
                holes.insert(id.clone());
            }
        }
        let expression = self.instantiate(expression)?;
        let mut work = vec![&expression];
        let mut seen = HashSet::new();
        while let Some(term) = work.pop() {
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            self.tick()?;
            match term.node() {
                ExprNode::MVar { id } if holes.contains(id) => return Ok(true),
                ExprNode::App { f, a } => work.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => work.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => work.extend([type_, value, body]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr),
                _ => {}
            }
        }
        Ok(false)
    }
}

enum LayoutVisit {
    Structure {
        name: Name,
        path: Vec<Projection>,
        ancestors: Vec<Name>,
    },
    Leaf(Leaf),
}

impl Context {
    fn checked_imported_structure<'a>(
        &mut self,
        structures: &'a ImportedStructures,
        name: &Name,
    ) -> Result<&'a StructureEntry, NatDefinitionElabError> {
        self.tick()?;
        let entry = structures.get(name).ok_or_else(malformed)?;
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name) else {
            return Err(malformed());
        };
        if family.is_unsafe || family.is_rec || family.num_indices != 0 || family.ctors.len() != 1 {
            return Err(malformed());
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&family.ctors[0]) else {
            return Err(malformed());
        };
        if ctor.is_unsafe
            || ctor.induct != *name
            || ctor.num_params != family.num_params
            || ctor.base.level_params != family.base.level_params
            || ctor.num_fields as usize != entry.fields.len()
        {
            return Err(malformed());
        }
        if entry.fields.len() > RecordBudget::default().max_binders
            || entry.parents.len() > RecordBudget::default().max_binders
        {
            return Err(limit());
        }
        Ok(entry)
    }

    fn imported_record_leaves(
        &mut self,
        structures: &ImportedStructures,
        root: &Name,
    ) -> Result<Vec<Leaf>, NatDefinitionElabError> {
        let mut work = vec![LayoutVisit::Structure {
            name: root.clone(),
            path: Vec::new(),
            ancestors: Vec::new(),
        }];
        let mut leaves = Vec::new();
        let mut names = BTreeSet::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                LayoutVisit::Leaf(leaf) => {
                    if !names.insert(leaf.name.clone()) {
                        return Err(error(RecordTermError::DuplicateField(leaf.name)));
                    }
                    if leaves.len() >= RecordBudget::default().max_binders {
                        return Err(limit());
                    }
                    leaves.push(leaf);
                }
                LayoutVisit::Structure {
                    name,
                    path,
                    mut ancestors,
                } => {
                    if ancestors.contains(&name) {
                        return Err(malformed());
                    }
                    if ancestors.len() >= RecordBudget::default().max_binders {
                        return Err(limit());
                    }
                    ancestors.push(name.clone());
                    let entry = self.checked_imported_structure(structures, &name)?.clone();
                    for (index, field) in entry.fields.into_iter().enumerate().rev() {
                        self.tick()?;
                        let mut field_path = path.clone();
                        field_path.push(Projection {
                            owner: name.clone(),
                            name: field.projection,
                            index: Some(u32::try_from(index).map_err(|_| limit())?),
                        });
                        if let Some(parent) = field.subobject {
                            work.push(LayoutVisit::Structure {
                                name: parent,
                                path: field_path,
                                ancestors: ancestors.clone(),
                            });
                        } else {
                            work.push(LayoutVisit::Leaf(Leaf {
                                name: field.name,
                                style: field.binder_info,
                                path: field_path,
                            }));
                        }
                    }
                }
            }
        }
        Ok(leaves)
    }

    /// The pin's relaxed C3 merge gives the direct parent list first priority.
    /// A completed order is memoized only within this immutable metadata read.
    pub(in crate::source) fn imported_parent_order(
        &mut self,
        structures: &ImportedStructures,
        root: &Name,
        source_parents: Option<&[Name]>,
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        let mut orders: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
        let mut visiting = BTreeSet::new();
        let mut work = vec![(root.clone(), false)];
        while let Some((name, finish)) = work.pop() {
            self.tick()?;
            if orders.contains_key(&name) {
                continue;
            }
            let direct: Vec<_> = if &name == root
                && let Some(parents) = source_parents
            {
                parents.to_vec()
            } else {
                self.checked_imported_structure(structures, &name)?
                    .parents
                    .iter()
                    .map(|parent| parent.name.clone())
                    .collect()
            };
            if !finish {
                if !visiting.insert(name.clone()) {
                    return Err(malformed());
                }
                if visiting.len() >= RecordBudget::default().max_binders {
                    return Err(limit());
                }
                work.push((name, true));
                for parent in direct.iter().rev() {
                    self.tick()?;
                    if !orders.contains_key(parent) {
                        work.push((parent.clone(), false));
                    }
                }
                continue;
            }
            let mut rows = vec![direct.clone()];
            for parent in direct {
                self.tick()?;
                rows.push(orders.get(&parent).cloned().ok_or_else(malformed)?);
            }
            rows.retain(|row| !row.is_empty());
            let mut order = vec![name.clone()];
            while !rows.is_empty() {
                self.tick()?;
                let mut selected = None;
                'selection: for dropped in 0..rows.len() {
                    let high = rows.len() - dropped;
                    for index in 0..high {
                        self.tick()?;
                        let candidate = &rows[index][0];
                        let mut consistent = true;
                        for (other, row) in rows.iter().take(high).enumerate() {
                            if other == index {
                                continue;
                            }
                            for inherited in row.iter().skip(1) {
                                self.tick()?;
                                if inherited == candidate {
                                    consistent = false;
                                    break;
                                }
                            }
                            if !consistent {
                                break;
                            }
                        }
                        if consistent {
                            selected = Some(candidate.clone());
                            break 'selection;
                        }
                    }
                }
                let selected = selected.ok_or_else(malformed)?;
                if order.len() >= RecordBudget::default().max_binders {
                    return Err(limit());
                }
                order.push(selected.clone());
                for row in &mut rows {
                    for _ in row.iter() {
                        self.tick()?;
                    }
                    row.retain(|name| name != &selected);
                }
                rows.retain(|row| !row.is_empty());
            }
            visiting.remove(&name);
            orders.insert(name, order);
        }
        orders.remove(root).ok_or_else(malformed)
    }

    fn imported_parent_path(
        &mut self,
        structures: &ImportedStructures,
        root: &Name,
        wanted: &Name,
    ) -> Result<Vec<Projection>, NatDefinitionElabError> {
        let mut work = vec![(root.clone(), Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((name, path)) = work.pop() {
            self.tick()?;
            if &name == wanted {
                return Ok(path);
            }
            if !seen.insert(name.clone()) {
                continue;
            }
            if path.len() >= RecordBudget::default().max_binders {
                return Err(limit());
            }
            let entry = self.checked_imported_structure(structures, &name)?.clone();
            // Physical subobjects take precedence over other parent views.
            for parent in entry.parents.iter().rev() {
                self.tick()?;
                let mut next = path.clone();
                next.push(Projection {
                    owner: name.clone(),
                    name: parent.projection.clone(),
                    index: None,
                });
                work.push((parent.name.clone(), next));
            }
            for (index, field) in entry.fields.iter().enumerate().rev() {
                self.tick()?;
                if let Some(parent) = &field.subobject {
                    let mut next = path.clone();
                    next.push(Projection {
                        owner: name.clone(),
                        name: field.projection.clone(),
                        index: Some(u32::try_from(index).map_err(|_| limit())?),
                    });
                    work.push((parent.clone(), next));
                }
            }
        }
        Err(malformed())
    }

    fn imported_project_path(
        &mut self,
        mut receiver: Typed,
        path: &[Projection],
    ) -> Result<Typed, NatDefinitionElabError> {
        for projection in path {
            self.tick()?;
            let target = self.whnf(&receiver.type_)?;
            let mut parameters = Vec::new();
            let mut head = &target;
            while let ExprNode::App { f, a } = head.node() {
                self.tick()?;
                parameters.push(a.clone());
                head = f;
            }
            parameters.reverse();
            let ExprNode::Const { name, levels } = head.node() else {
                return Err(malformed());
            };
            if name != &projection.owner {
                return Err(malformed());
            }
            let (base, value) = match self.txn.env.find(&projection.name).cloned() {
                Some(ConstantInfo::Defn(definition))
                    if definition.safety == DefinitionSafety::Safe =>
                {
                    (definition.base, definition.value)
                }
                Some(ConstantInfo::Thm(theorem)) => (theorem.base, theorem.value),
                _ => return Err(malformed()),
            };
            if base.level_params.len() != levels.len() {
                return Err(malformed());
            }
            let mut projected = Typed {
                value: self.instantiate_params(&value, &base.level_params, levels)?,
                type_: self.instantiate_params(&base.type_, &base.level_params, levels)?,
            };
            parameters.push(receiver.value);
            for parameter in parameters {
                self.apply_imported_record_body(&mut projected, &parameter)?;
            }
            if let Some(index) = projection.index
                && !matches!(projected.value.node(), ExprNode::Proj { struct_name, idx, .. }
                    if struct_name == &projection.owner && *idx == u64::from(index))
            {
                return Err(malformed());
            }
            let value = self.whnf(&projected.value)?;
            let type_ = self.known_type(&value)?.ok_or_else(malformed)?;
            self.constrain(&type_, &projected.type_)?;
            receiver = Typed { value, type_ };
        }
        Ok(receiver)
    }
}
