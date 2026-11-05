//! The pin's `_flat_ctor`: ordinary checked definitions whose arguments are the
//! non-parent fields in constructor order. Parent subobjects are rebuilt by
//! applying their admitted constructors, including dependent parent telescopes.
use super::parents::Inheritance;
use super::*;
use crate::records::imported::ImportedStructures;
use crate::records::inheritance::RecordParents;
use fln_env::constants::ConstantInfo;
use fln_syntax::source::SourceInfo;
use std::collections::HashSet;

struct Frame {
    record: Name,
    value: Expr,
    type_: Expr,
    index: u32,
    fields: u32,
}

fn problem(error: crate::records::RecordError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Record(error))
}

impl Context {
    fn flat_parent_frame(&mut self, type_: Expr) -> Result<Frame, NatDefinitionElabError> {
        let type_ = self.whnf(&type_)?;
        let mut head = &type_;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        arguments.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        };
        if family.is_unsafe
            || family.is_rec
            || family.num_indices != 0
            || family.ctors.len() != 1
            || arguments.len() != family.num_params as usize
            || levels.len() != family.base.level_params.len()
        {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&family.ctors[0]).cloned() else {
            return Err(problem(crate::records::RecordError::InvalidTelescope));
        };
        let mut frame = Frame {
            record: name.clone(),
            value: Expr::const_(ctor.base.name.clone(), levels.clone()),
            type_: self.instantiate_params(&ctor.base.type_, &ctor.base.level_params, levels)?,
            index: 0,
            fields: ctor.num_fields,
        };
        for argument in arguments {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = frame.type_.node() else {
                return Err(problem(crate::records::RecordError::InvalidTelescope));
            };
            frame.type_ = self.substitute(body, &argument)?;
            frame.value = Expr::app(frame.value, argument);
        }
        Ok(frame)
    }

    /// Open the checked parent telescopes into fresh flat fields. The child's
    /// constructor is only a spine builder here; it is not looked up or admitted.
    fn record_flat_fields(
        &mut self,
        spec: &RecordSpec,
        inheritance: &Inheritance,
        budget: RecordBudget,
    ) -> Result<(Vec<LocalDecl>, Expr), NatDefinitionElabError> {
        let registry = RecordParents::read(&self.txn.env).map_err(problem)?;
        let mut closer = crate::records::Builder {
            remaining: budget.max_nodes,
        };
        let levels: Vec<_> = spec
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let parameters: Vec<_> = spec
            .parameters
            .iter()
            .map(|p| Expr::fvar(p.id.clone()))
            .collect();
        let target = parameters
            .iter()
            .cloned()
            .fold(Expr::const_(spec.name.clone(), levels.clone()), Expr::app);
        let ctor_name = Name::str(spec.name.clone(), "mk");
        let value = parameters
            .into_iter()
            .fold(Expr::const_(ctor_name.clone(), levels), Expr::app);
        let type_ = closer
            .close(&spec.fields, target.clone(), false, false)
            .map_err(problem)?;
        let mut frames = vec![Frame {
            record: spec.name.clone(),
            value,
            type_,
            index: 0,
            fields: u32::try_from(spec.fields.len())
                .map_err(|_| problem(crate::records::RecordError::ResourceLimit))?,
        }];
        let mut fields = Vec::new();
        let mut labels = HashSet::new();
        let value = loop {
            self.tick()?;
            closer.tick().map_err(problem)?;
            let frame = frames
                .last_mut()
                .ok_or_else(|| problem(crate::records::RecordError::InvalidTelescope))?;
            if frame.index == frame.fields {
                let value = frames.pop().expect("nonempty frame stack").value;
                let Some(parent) = frames.last_mut() else {
                    break value;
                };
                let ExprNode::ForallE { body, .. } = parent.type_.node() else {
                    return Err(problem(crate::records::RecordError::InvalidTelescope));
                };
                parent.type_ = self.substitute(body, &value)?;
                parent.value = Expr::app(parent.value.clone(), value);
                parent.index += 1;
                continue;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                binder_info,
                body,
            } = frame.type_.node()
            else {
                return Err(problem(crate::records::RecordError::InvalidTelescope));
            };
            let rows = if frame.record == spec.name {
                &inheritance.parents
            } else {
                registry.parents(&frame.record)
            };
            if let Some(parent) = rows.iter().find(|parent| parent.field == frame.index) {
                let nested = self.flat_parent_frame(binder_type.clone())?;
                if nested.record != parent.parent {
                    return Err(problem(crate::records::RecordError::InvalidTelescope));
                }
                if frames.len() >= budget.max_binders {
                    return Err(problem(crate::records::RecordError::ResourceLimit));
                }
                frames.push(nested);
                continue;
            }
            if !labels.insert(binder_name.clone()) {
                return Err(problem(crate::records::RecordError::DuplicateField));
            }
            if spec
                .parameters
                .len()
                .saturating_add(fields.len())
                .saturating_add(1)
                > budget.max_binders
            {
                return Err(problem(crate::records::RecordError::ResourceLimit));
            }
            let id = FVarId(self.fresh_name()?);
            let domain = self.reduce_record_projections(binder_type)?;
            let local = self
                .txn
                .lctx
                .add_param(id.clone(), binder_name.clone(), domain, *binder_info)
                .clone();
            let value = Expr::fvar(id);
            frame.type_ = self.substitute(body, &value)?;
            frame.value = Expr::app(frame.value.clone(), value);
            frame.index += 1;
            fields.push(local);
        };
        Ok((fields, value))
    }

    /// Translate a physical field or parent alias into the newly opened flat
    /// telescope without unfolding arbitrary user definitions.
    fn flatten_record_value(
        &mut self,
        expression: Expr,
        spec: &RecordSpec,
        inheritance: &Inheritance,
        physical: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut expression = self.expand_record_aliases(expression, &inheritance.aliases)?;
        for (field, argument) in spec.fields.iter().zip(physical).rev() {
            self.tick()?;
            expression = expression
                .abstract_fvar(&field.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            expression = self.substitute(&expression, argument)?;
        }
        let expression = self.instantiate(&expression)?;
        self.reduce_record_projections(&expression)
    }

    /// Elaborate child-authored defaults with the complete flat field context.
    /// The target and every local depending on it are absent while the RHS is
    /// elaborated, including uses that a tactic would erase from its result.
    pub(super) fn record_default_overrides(
        &mut self,
        spec: &RecordSpec,
        inheritance: &Inheritance,
        overrides: &[DefaultOverride],
        budget: RecordBudget,
    ) -> Result<Vec<Declaration>, NatDefinitionElabError> {
        let structures = ImportedStructures::read(&self.txn.env).map_err(problem)?;
        let mut pending: Vec<_> = inheritance
            .direct
            .iter()
            .map(|(name, _, _)| name.clone())
            .collect();
        let mut seen = HashSet::new();
        while let Some(parent) = pending.pop() {
            self.tick()?;
            if !seen.insert(parent.clone()) {
                continue;
            }
            let Some(entry) = structures.get(&parent) else {
                return Err(problem(crate::records::RecordError::InvalidTelescope));
            };
            pending.extend(entry.parents.iter().map(|parent| parent.name.clone()));
        }
        let (fields, constructor) = self.record_flat_fields(spec, inheritance, budget)?;
        let (_, arguments) = operators::spine(&constructor);
        let physical = arguments
            .get(spec.parameters.len()..)
            .filter(|arguments| arguments.len() == spec.fields.len())
            .ok_or_else(|| problem(crate::records::RecordError::InvalidTelescope))?;
        let labels: HashSet<_> = fields.iter().map(|field| field.user_name.clone()).collect();
        // Parent values remain usable only when they do not depend on the
        // overridden leaf. Rebuild them as lets over the fresh flat variables,
        // rather than retaining the old physical parent parameters.
        let mut aliases = Vec::new();
        for (field, value) in spec.fields.iter().zip(physical) {
            self.tick()?;
            if labels.contains(&field.user_name) {
                continue;
            }
            let type_ =
                self.flatten_record_value(field.type_.clone(), spec, inheritance, physical)?;
            aliases.push(
                self.txn
                    .lctx
                    .add_let(
                        field.id.clone(),
                        field.user_name.clone(),
                        type_,
                        value.clone(),
                    )
                    .clone(),
            );
        }
        for alias in &inheritance.aliases {
            self.tick()?;
            if labels.contains(&alias.user_name) {
                continue;
            }
            let value = alias
                .value
                .clone()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let type_ =
                self.flatten_record_value(alias.type_.clone(), spec, inheritance, physical)?;
            let value = self.flatten_record_value(value, spec, inheritance, physical)?;
            aliases.push(
                self.txn
                    .lctx
                    .add_let(alias.id.clone(), alias.user_name.clone(), type_, value)
                    .clone(),
            );
        }
        if self.txn.lctx.len() > budget.max_binders {
            return Err(problem(crate::records::RecordError::ResourceLimit));
        }
        let full = self.txn.lctx.clone();
        let field_ids: HashSet<_> = fields
            .iter()
            .chain(&aliases)
            .map(|local| local.id.clone())
            .collect();
        let mut closer = crate::records::Builder {
            remaining: budget.max_nodes,
        };
        let mut declarations = Vec::new();
        for view in overrides {
            self.tick()?;
            let Some(field) = fields.iter().find(|field| field.user_name == view.name) else {
                // Direct and indirect parent projections are not leaf defaults.
                return Err(problem(crate::records::RecordError::DuplicateField));
            };
            let signature = expect_node(
                &view.signature,
                &parser_kind(&["Command", "optDeclSig"]),
                2,
                "inherited field signature",
            )?;
            let binders = expect_null_args(&signature[0], "inherited field binders")?;
            self.refuse_default_parameter_binders(binders, &field_ids)?;
            let annotation = optional_type_syntax(&signature[1])?;
            if view.tactic && (!binders.is_empty() || annotation.is_some()) {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "an inherited field tactic without a type or binders",
                });
            }
            if !view.from_subobject && (!binders.is_empty() || annotation.is_some()) {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "a copied field default without a new type or binders",
                });
            }
            let mut syntax = view.value.clone();
            if let Some(annotation) = annotation {
                syntax = Syntax::node(
                    parser_kind(&["Term", "typeAscription"]),
                    vec![
                        Syntax::atom(SourceInfo::None, "("),
                        syntax,
                        Syntax::atom(SourceInfo::None, ":"),
                        Syntax::node(Name::from_components(["null"]), vec![annotation.clone()]),
                        Syntax::atom(SourceInfo::None, ")"),
                    ],
                );
            }
            if !binders.is_empty() {
                syntax = Syntax::node(
                    parser_kind(&["Term", "fun"]),
                    vec![
                        Syntax::atom(SourceInfo::None, "fun"),
                        Syntax::node(
                            parser_kind(&["Term", "basicFun"]),
                            vec![
                                signature[0].clone(),
                                Syntax::node(Name::from_components(["null"]), Vec::new()),
                                Syntax::atom(SourceInfo::None, "=>"),
                                syntax,
                            ],
                        ),
                    ],
                );
            }
            let mut removed = HashSet::from([field.id.clone()]);
            let mut scope = LocalContext::new();
            for local in full.decls() {
                self.tick()?;
                let mut reads = self.elimination_reads(&local.type_)?;
                if let Some(value) = &local.value {
                    reads.extend(self.elimination_reads(value)?);
                }
                if removed.contains(&local.id) || reads.iter().any(|id| removed.contains(id)) {
                    removed.insert(local.id.clone());
                    continue;
                }
                if let Some(value) = &local.value {
                    scope.add_let(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        value.clone(),
                    );
                } else {
                    scope.add_param(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        local.binder_info,
                    );
                }
            }
            self.txn.lctx = scope;
            let infer_levels = self.infer_level_params;
            self.infer_level_params = false;
            let result = self
                .term(&syntax, Some(field.type_.clone()))
                .and_then(|term| {
                    self.finish(Typed {
                        value: term.value,
                        type_: field.type_.clone(),
                    })
                });
            self.infer_level_params = infer_levels;
            self.txn.lctx = full.clone();
            let mut selected = result?;
            selected.value = self.expand_record_aliases(selected.value, &aliases)?;
            selected.type_ = self.expand_record_aliases(selected.type_, &aliases)?;
            selected.value = self.reduce_record_projections(&selected.value)?;
            selected.type_ = self.reduce_record_projections(&selected.type_)?;
            declarations.push(self.close_record_flat_default(
                spec,
                &fields,
                selected,
                helper_name(&spec.name, &field.user_name),
                &mut closer,
            )?);
        }
        Ok(declarations)
    }

    /// The pin reads leading typeless bracketed binders as parameter updates.
    /// Any such update is forbidden for an inherited default. The first group
    /// suffices: a non-parameter group ends that prefix, and an update refuses.
    fn refuse_default_parameter_binders(
        &mut self,
        binders: &[Syntax],
        fields: &HashSet<FVarId>,
    ) -> Result<(), NatDefinitionElabError> {
        let Some(binder) = binders.first() else {
            return Ok(());
        };
        self.tick()?;
        let Some(kind) = binder.kind() else {
            return Ok(());
        };
        let names = if kind == &parser_kind(&["Term", "explicitBinder"])
            || kind == &parser_kind(&["Term", "implicitBinder"])
            || kind == &parser_kind(&["Term", "strictImplicitBinder"])
        {
            let explicit = kind == &parser_kind(&["Term", "explicitBinder"]);
            let parts = expect_node(
                binder,
                kind,
                if explicit { 5 } else { 4 },
                "inherited field binder",
            )?;
            if !expect_null_args(&parts[2], "inherited binder type")?.is_empty()
                || (explicit
                    && !expect_null_args(&parts[3], "inherited binder default")?.is_empty())
            {
                return Ok(());
            }
            expect_null_args(&parts[1], "inherited binder names")?
        } else if kind == &parser_kind(&["Term", "instBinder"]) {
            let parts = expect_node(binder, kind, 4, "inherited instance binder")?;
            if !expect_null_args(&parts[1], "inherited instance name")?.is_empty() {
                return Ok(());
            }
            std::slice::from_ref(&parts[2])
        } else {
            // Bare identifiers and typed groups introduce ordinary lambda binders.
            return Ok(());
        };
        if names.is_empty() {
            return Ok(());
        }
        for name in names {
            self.tick()?;
            let Syntax::Ident { val, .. } = name else {
                return Ok(());
            };
            let Some(local) = self.txn.lctx.find_by_user_name(val) else {
                return Ok(());
            };
            if fields.contains(&local.id) {
                return Ok(());
            }
        }
        // Section locals also refuse: only written header parameters could be
        // updated at the pin, and inherited defaults allow no updates at all.
        Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "inherited default binders without parameter binder-kind updates",
        })
    }

    fn close_record_flat_default(
        &mut self,
        spec: &RecordSpec,
        fields: &[LocalDecl],
        mut selected: Typed,
        name: Name,
        closer: &mut crate::records::Builder,
    ) -> Result<Declaration, NatDefinitionElabError> {
        // Stop the default reader's field-name scan before a method's binders.
        selected.value = Expr::app(
            Expr::lam(
                Name::anonymous(),
                selected.type_.clone(),
                Expr::bvar(0).map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            ),
            selected.value,
        );
        let mut used = self.elimination_reads(&selected.value)?;
        used.extend(self.elimination_reads(&selected.type_)?);
        let mut dependencies = Vec::new();
        for local in fields.iter().rev() {
            self.tick()?;
            if used.contains(&local.id) {
                used.extend(self.elimination_reads(&local.type_)?);
                let mut local = local.clone();
                local.binder_info = BinderInfo::Default;
                dependencies.push(local);
            }
        }
        dependencies.reverse();
        let value = closer
            .close(&dependencies, selected.value, true, false)
            .map_err(problem)?;
        let type_ = closer
            .close(&dependencies, selected.type_, false, false)
            .map_err(problem)?;
        let value = closer
            .close(&spec.parameters, value, true, true)
            .map_err(problem)?;
        let type_ = closer
            .close(&spec.parameters, type_, false, true)
            .map_err(problem)?;
        Ok(Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: spec.level_params.clone(),
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name],
        }))
    }

    pub(super) fn record_flat_constructor(
        &mut self,
        spec: &RecordSpec,
        inheritance: &Inheritance,
        declared_defaults: &[Name],
        budget: RecordBudget,
    ) -> Result<Vec<Declaration>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let (fields, value) = self.record_flat_fields(spec, inheritance, budget)?;
            let mut closer = crate::records::Builder {
                remaining: budget.max_nodes,
            };
            let target = spec.parameters.iter().fold(
                Expr::const_(
                    spec.name.clone(),
                    spec.level_params
                        .iter()
                        .cloned()
                        .map(Level::param)
                        .collect(),
                ),
                |target, parameter| Expr::app(target, Expr::fvar(parameter.id.clone())),
            );
            let ctor_name = Name::str(spec.name.clone(), "mk");
            let mut declarations = self.record_flat_inherited_defaults(
                spec,
                inheritance,
                declared_defaults,
                &fields,
                &value,
                &mut closer,
            )?;
            let type_ = closer
                .close(&fields, target, false, false)
                .map_err(problem)?;
            let type_ = closer
                .close(&spec.parameters, type_, false, true)
                .map_err(problem)?;
            let value = closer.close(&fields, value, true, false).map_err(problem)?;
            let value = closer
                .close(&spec.parameters, value, true, true)
                .map_err(problem)?;
            let name = Name::str(ctor_name, "_flat_ctor");
            declarations.insert(
                0,
                Declaration::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: name.clone(),
                        level_params: spec.level_params.clone(),
                        type_,
                    },
                    value,
                    hints: ReducibilityHints::Abbrev,
                    safety: DefinitionSafety::Safe,
                    all: vec![name],
                }),
            );
            Ok(declarations)
        })();
        self.txn.lctx = saved;
        result
    }

    /// Freeze only declared defaults, in relaxed C3 order. Inherited helpers
    /// from an intermediate parent are deliberately not fresh declarations.
    fn record_flat_inherited_defaults(
        &mut self,
        spec: &RecordSpec,
        inheritance: &Inheritance,
        declared_defaults: &[Name],
        fields: &[LocalDecl],
        constructor: &Expr,
        closer: &mut crate::records::Builder,
    ) -> Result<Vec<Declaration>, NatDefinitionElabError> {
        if inheritance.direct.is_empty() {
            return Ok(Vec::new());
        }
        let structures = ImportedStructures::read(&self.txn.env).map_err(problem)?;
        let direct: Vec<_> = inheritance
            .direct
            .iter()
            .map(|(name, _, _)| name.clone())
            .collect();
        // Legacy seed dictionaries can occur anywhere in the ancestry and have
        // only a native physical interface. Keep their existing source path.
        let mut pending = direct.clone();
        let mut seen = HashSet::new();
        while let Some(parent) = pending.pop() {
            self.tick()?;
            if !seen.insert(parent.clone()) {
                continue;
            }
            let Some(entry) = structures.get(&parent) else {
                return Ok(Vec::new());
            };
            pending.extend(entry.parents.iter().map(|parent| parent.name.clone()));
        }
        let order = self.imported_parent_order(&structures, &spec.name, Some(&direct))?;
        let (_, arguments) = operators::spine(constructor);
        let physical = arguments
            .get(spec.parameters.len()..)
            .filter(|arguments| arguments.len() == spec.fields.len())
            .ok_or_else(|| problem(crate::records::RecordError::InvalidTelescope))?;
        let mut parents = Vec::new();
        for (parent, label, subobject) in &inheritance.direct {
            self.tick()?;
            let mut receiver = if *subobject {
                let field = spec
                    .fields
                    .iter()
                    .find(|field| &field.user_name == label)
                    .ok_or_else(|| problem(crate::records::RecordError::InvalidTelescope))?;
                Typed {
                    value: Expr::fvar(field.id.clone()),
                    type_: field.type_.clone(),
                }
            } else {
                let copied = inheritance
                    .copied
                    .iter()
                    .find(|copied| &copied.parent == parent && &copied.label == label)
                    .ok_or_else(|| problem(crate::records::RecordError::InvalidTelescope))?;
                Typed {
                    value: copied.value.clone(),
                    type_: copied.type_.clone(),
                }
            };
            receiver.value = self.expand_record_aliases(receiver.value, &inheritance.aliases)?;
            receiver.type_ = self.expand_record_aliases(receiver.type_, &inheritance.aliases)?;
            for (field, argument) in spec.fields.iter().zip(physical).rev() {
                self.tick()?;
                receiver.value = receiver
                    .value
                    .abstract_fvar(&field.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                receiver.type_ = receiver
                    .type_
                    .abstract_fvar(&field.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                receiver.value = self.substitute(&receiver.value, argument)?;
                receiver.type_ = self.substitute(&receiver.type_, argument)?;
            }
            receiver.value = self.instantiate(&receiver.value)?;
            receiver.type_ = self.instantiate(&receiver.type_)?;
            receiver.value = self.reduce_record_projections(&receiver.value)?;
            receiver.type_ = self.reduce_record_projections(&receiver.type_)?;
            parents.push((parent.clone(), receiver));
        }
        let arguments: Vec<_> = fields
            .iter()
            .map(|field| (field.user_name.clone(), Expr::fvar(field.id.clone())))
            .collect();
        let mut declarations = Vec::new();
        for field in fields {
            self.tick()?;
            let declared = helper_name(&spec.name, &field.user_name);
            if declared_defaults.contains(&declared) {
                continue;
            }
            let mut selected = None;
            for owner in order.iter().skip(1) {
                self.tick()?;
                let helper = helper_name(owner, &field.user_name);
                if !self.txn.env.contains(&helper)
                    || !self.record_has_flat_field(&structures, owner, &field.user_name)?
                {
                    continue;
                }
                let receiver = self.source_record_parent_view(&structures, &parents, owner)?;
                selected = self.instantiate_record_default(&helper, &receiver, &arguments)?;
                if selected.is_some() {
                    break;
                }
            }
            let Some(selected) = selected else {
                continue;
            };
            if !self.defeq_guarded(&selected.type_, &field.type_)? {
                return Err(problem(crate::records::RecordError::InvalidTelescope));
            }
            let name = Name::str(
                spec.name.append_core(&field.user_name),
                "_inherited_default",
            );
            declarations
                .push(self.close_record_flat_default(spec, fields, selected, name, closer)?);
        }
        Ok(declarations)
    }
}
