//! Named record construction. Field names select constructor arguments, never
//! independent declarations or trusted projections. Elaboration follows the
//! constructor telescope so later field types see the actual earlier values.
use super::*;
use fln_core::name::LeafView;
use fln_env::constants::ConstantInfo;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordTermError {
    ExpectedRecordType,
    UnknownField(Name),
    DuplicateField(Name),
    MissingField(Name),
}
impl std::fmt::Display for RecordTermError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpectedRecordType => f.write_str(
                "record construction requires a known nonrecursive single-constructor type",
            ),
            Self::UnknownField(name) => {
                write!(f, "unknown record field {}", name.to_display_string())
            }
            Self::DuplicateField(name) => {
                write!(f, "duplicate record field {}", name.to_display_string())
            }
            Self::MissingField(name) => {
                write!(f, "missing record field {}", name.to_display_string())
            }
        }
    }
}
fn error(reason: RecordTermError) -> NatDefinitionElabError {
    failure(SourceInferenceError::RecordTerm(reason))
}

pub(super) struct RecordParts<'a> {
    fields: Vec<(Name, &'a Syntax)>,
    pub(super) annotation: Option<&'a Syntax>,
    pub(super) sources: Vec<&'a Syntax>,
}
pub(super) struct RecordBuild<'a> {
    fields: HashMap<Name, &'a Syntax>,
    constructor: Typed,
    remaining: u32,
    expected: Expr,
    sources: Vec<Typed>,
    source_bindings: Vec<LocalDecl>,
    saved_lctx: LocalContext,
}
pub(super) enum RecordStep<'a> {
    Field {
        syntax: &'a Syntax,
        domain: Expr,
        codomain: Expr,
    },
    Copy {
        value: Typed,
        codomain: Expr,
    },
    Complete(Typed),
}

impl Context {
    /// Resolve a qualified identifier only after exact local/global lookup has
    /// failed. Names are split structurally: an escaped dot is never a separator.
    pub(super) fn qualified_record_field(
        &mut self,
        name: &Name,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let mut prefix = name.clone();
        let mut suffix = Vec::new();
        while !prefix.is_anonymous() {
            self.tick()?;
            let LeafView::Str(part) = prefix.leaf_view() else {
                return Ok(None);
            };
            suffix.push(Name::from_components([part]));
            prefix = prefix.parent().clone();
            let receiver = if let Some(local) = self
                .txn
                .lctx
                .decls()
                .iter()
                .rev()
                .find(|local| local.user_name == prefix)
            {
                Some(Typed {
                    value: Expr::fvar(local.id.clone()),
                    type_: local.type_.clone(),
                })
            } else if self.txn.env.contains(&prefix) {
                Some(self.constant(&prefix)?)
            } else {
                None
            };
            if let Some(mut receiver) = receiver {
                for (index, field) in suffix.iter().rev().enumerate() {
                    receiver = match self.record_field(receiver, field) {
                        Ok(term) => term,
                        Err(NatDefinitionElabError::Inference(
                            SourceInferenceError::RecordTerm(RecordTermError::ExpectedRecordType),
                        )) if index == 0 => {
                            // A namespace prefix such as Nat is not a receiver.
                            // Keep its missing constant on the original path.
                            return Ok(None);
                        }
                        Err(error) => return Err(error),
                    };
                }
                return Ok(Some(receiver));
            }
        }
        Ok(None)
    }

    /// Apply admitted generated projections to the actual receiver. In
    /// particular, an instance-implicit class receiver must not be replaced by
    /// a dictionary selected from the surrounding context.
    pub(super) fn record_field_path(
        &mut self,
        mut receiver: Typed,
        path: &Name,
    ) -> Result<Typed, NatDefinitionElabError> {
        let mut parts = Vec::new();
        let mut name = path.clone();
        while !name.is_anonymous() {
            self.tick()?;
            let LeafView::Str(part) = name.leaf_view() else {
                return Err(error(RecordTermError::UnknownField(path.clone())));
            };
            parts.push(Name::from_components([part]));
            name = name.parent().clone();
        }
        if parts.is_empty() {
            return Err(failure(SourceInferenceError::Scope));
        }
        for part in parts.iter().rev() {
            receiver = self.record_field(receiver, part)?;
        }
        Ok(receiver)
    }

    fn record_field(
        &mut self,
        receiver: Typed,
        field: &Name,
    ) -> Result<Typed, NatDefinitionElabError> {
        // Field access opens ordinary implicit/instance arguments, but is not
        // an explicit argument that would trigger strict-implicit insertion.
        let receiver = self.insert_implicits(receiver, ImplicitInsertion::FieldReceiver)?;
        self.flush(false)?;
        // A known dictionary can determine the record's type itself. Unknown
        // inputs stay deferred until the selected field receives its context.
        self.resolve_instances(false)?;
        let target = self.whnf(&receiver.type_)?;
        let mut head = &target;
        let mut params = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            params.push(a.clone());
            head = f;
        }
        params.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(error(RecordTermError::ExpectedRecordType));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(error(RecordTermError::ExpectedRecordType));
        };
        if family.is_unsafe
            || family.is_rec
            || family.num_indices != 0
            || family.ctors.len() != 1
            || params.len() != family.num_params as usize
            || levels.len() != family.base.level_params.len()
        {
            return Err(error(RecordTermError::ExpectedRecordType));
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&family.ctors[0]).cloned() else {
            return Err(error(RecordTermError::ExpectedRecordType));
        };
        if ctor.is_unsafe || ctor.induct != *name || ctor.num_params != family.num_params {
            return Err(error(RecordTermError::ExpectedRecordType));
        }
        let mut telescope = &ctor.base.type_;
        let mut found = false;
        for index in 0..u64::from(ctor.num_params) + u64::from(ctor.num_fields) {
            self.tick()?;
            let ExprNode::ForallE {
                binder_name, body, ..
            } = telescope.node()
            else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if index >= u64::from(ctor.num_params) && binder_name == field {
                found = true;
            }
            telescope = body;
        }
        if !found {
            return Err(error(RecordTermError::UnknownField(field.clone())));
        }
        let projection_name = name.append_core(field);
        let Some(ConstantInfo::Defn(projection)) = self.txn.env.find(&projection_name).cloned()
        else {
            return Err(error(RecordTermError::UnknownField(field.clone())));
        };
        if projection.safety != DefinitionSafety::Safe
            || projection.base.level_params.len() != levels.len()
        {
            return Err(error(RecordTermError::UnknownField(field.clone())));
        }
        let mut term = Typed {
            value: Expr::const_(projection_name, levels.clone()),
            type_: self.instantiate_params(
                &projection.base.type_,
                &projection.base.level_params,
                levels,
            )?,
        };
        params.push(receiver.value);
        for argument in params {
            self.tick()?;
            let type_ = self.whnf(&term.type_)?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Err(failure(SourceInferenceError::Scope));
            };
            term.type_ = self.substitute(body, &argument)?;
            term.value = Expr::app(term.value, argument);
        }
        Ok(term)
    }

    pub(super) fn record_parts<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<RecordParts<'a>, NatDefinitionElabError> {
        let parts = expect_node(
            syntax,
            &parser_kind(&["Term", "structInst"]),
            6,
            "record initializer",
        )?;
        expect_atom(&parts[0], "{", "record opener")?;
        expect_atom(&parts[5], "}", "record closer")?;
        let mut sources = Vec::new();
        match expect_null_args(&parts[1], "record update sources")? {
            [] => {}
            [items, keyword] => {
                expect_atom(keyword, "with", "record update keyword")?;
                let rows = expect_null_args(items, "record update source list")?;
                if rows.is_empty() || rows.len() % 2 == 0 {
                    return Err(failure(SourceInferenceError::Scope));
                }
                for (index, term) in rows.iter().enumerate() {
                    self.tick()?;
                    if index % 2 == 0 {
                        sources.push(term);
                    } else {
                        expect_atom(term, ",", "record source separator")?;
                    }
                }
            }
            _ => return Err(failure(SourceInferenceError::Scope)),
        }
        let ellipsis = expect_node(
            &parts[3],
            &parser_kind(&["Term", "optEllipsis"]),
            1,
            "record ellipsis",
        )?;
        expect_empty_null(&ellipsis[0], "unsupported record ellipsis")?;
        let annotation = match expect_null_args(&parts[4], "record type annotation")? {
            [] => None,
            [colon, type_] => {
                expect_atom(colon, ":", "record annotation colon")?;
                Some(type_)
            }
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        let wrapper = expect_node(
            &parts[2],
            &parser_kind(&["Term", "structInstFields"]),
            1,
            "record fields",
        )?;
        let mut fields = Vec::new();
        let mut names = std::collections::HashSet::new();
        for (index, syntax) in expect_null_args(&wrapper[0], "record field rows")?
            .iter()
            .enumerate()
        {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(syntax, ",", "record field separator")?;
                continue;
            }
            let field = expect_node(
                syntax,
                &parser_kind(&["Term", "structInstField"]),
                2,
                "record field",
            )?;
            let label = expect_node(
                &field[0],
                &parser_kind(&["Term", "structInstLVal"]),
                2,
                "field label",
            )?;
            expect_empty_null(&label[1], "unsupported nested field path")?;
            let Syntax::Ident { val: name, .. } = &label[0] else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if !names.insert(name.clone()) {
                return Err(error(RecordTermError::DuplicateField(name.clone())));
            }
            let value = match expect_null_args(&field[1], "field value")? {
                [] => &label[0],
                [binders, annotation, value] => {
                    expect_empty_null(binders, "unsupported field method binders")?;
                    expect_empty_null(annotation, "unsupported field value annotation")?;
                    let value = expect_node(
                        value,
                        &parser_kind(&["Term", "structInstFieldDef"]),
                        3,
                        "field assignment",
                    )?;
                    expect_atom(&value[0], ":=", "field assignment token")?;
                    expect_empty_null(&value[1], "unsupported private field value")?;
                    &value[2]
                }
                _ => return Err(failure(SourceInferenceError::Scope)),
            };
            fields.push((name.clone(), value));
        }
        Ok(RecordParts {
            fields,
            annotation,
            sources,
        })
    }

    pub(super) fn start_record<'a>(
        &mut self,
        parts: RecordParts<'a>,
        expected: Option<Expr>,
        sources: Vec<Typed>,
    ) -> Result<RecordBuild<'a>, NatDefinitionElabError> {
        self.flush(false)?;
        let expected = expected
            .or_else(|| sources.first().map(|source| source.type_.clone()))
            .ok_or_else(|| error(RecordTermError::ExpectedRecordType))?;
        let target = self.whnf(&expected)?;
        let mut head = &target;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        arguments.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(error(RecordTermError::ExpectedRecordType));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(error(RecordTermError::ExpectedRecordType));
        };
        if family.is_rec
            || family.is_unsafe
            || family.num_indices != 0
            || family.ctors.len() != 1
            || arguments.len() != family.num_params as usize
            || levels.len() != family.base.level_params.len()
        {
            return Err(error(RecordTermError::ExpectedRecordType));
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&family.ctors[0]).cloned() else {
            return Err(error(RecordTermError::ExpectedRecordType));
        };
        if ctor.is_unsafe || ctor.induct != *name || ctor.num_params != family.num_params {
            return Err(error(RecordTermError::ExpectedRecordType));
        }
        let mut constructor = Typed {
            value: Expr::const_(ctor.base.name.clone(), levels.clone()),
            type_: self.instantiate_params(&ctor.base.type_, &ctor.base.level_params, levels)?,
        };
        for arg in arguments {
            self.tick()?;
            let type_ = self.whnf(&constructor.type_)?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Err(failure(SourceInferenceError::Scope));
            };
            constructor.type_ = self.substitute(body, &arg)?;
            constructor.value = Expr::app(constructor.value, arg);
        }
        // Check the complete label inventory before elaborating any field.
        // Validation walks binder bodies without reducing open bound variables.
        let mut known = std::collections::HashSet::new();
        let mut cursor = &constructor.type_;
        for _ in 0..ctor.num_fields {
            self.tick()?;
            let ExprNode::ForallE {
                binder_name, body, ..
            } = cursor.node()
            else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if !known.insert(binder_name.clone()) {
                return Err(error(RecordTermError::ExpectedRecordType));
            }
            cursor = body;
        }
        for (label, _) in &parts.fields {
            if !known.contains(label) {
                return Err(error(RecordTermError::UnknownField(label.clone())));
            }
        }
        // Bind update sources exactly once. Even an unused source remains a
        // checked let value, so an ill-typed update source cannot disappear.
        let saved_lctx = self.txn.lctx.clone();
        let mut source_bindings = Vec::new();
        let mut bound_sources = Vec::new();
        for source in sources {
            self.tick()?;
            let type_ = self.whnf(&source.type_)?;
            let mut head = &type_;
            let mut params = 0_u32;
            while let ExprNode::App { f, .. } = head.node() {
                self.tick()?;
                params = params
                    .checked_add(1)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                head = f;
            }
            let ExprNode::Const { name, levels } = head.node() else {
                return Err(error(RecordTermError::ExpectedRecordType));
            };
            if !matches!(self.txn.env.find(name), Some(ConstantInfo::Induct(family))
                if !family.is_unsafe && !family.is_rec && family.num_indices == 0
                && family.ctors.len() == 1 && params == family.num_params
                && levels.len() == family.base.level_params.len())
            {
                return Err(error(RecordTermError::ExpectedRecordType));
            }
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_let(
                id.clone(),
                Name::anonymous(),
                source.type_.clone(),
                source.value,
            );
            source_bindings.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("inserted source binding")
                    .clone(),
            );
            bound_sources.push(Typed {
                value: Expr::fvar(id),
                type_: source.type_,
            });
        }
        Ok(RecordBuild {
            fields: parts.fields.into_iter().collect(),
            constructor,
            remaining: ctor.num_fields,
            expected,
            sources: bound_sources,
            source_bindings,
            saved_lctx,
        })
    }

    pub(super) fn next_record_field<'a>(
        &mut self,
        state: &mut RecordBuild<'a>,
    ) -> Result<RecordStep<'a>, NatDefinitionElabError> {
        self.tick()?;
        if state.remaining == 0 {
            if !state.fields.is_empty() {
                return Err(failure(SourceInferenceError::Scope));
            }
            let mut term = self.finish_term(state.constructor.clone(), Some(&state.expected))?;
            term.value = self.instantiate(&term.value)?;
            term.type_ = self.instantiate(&term.type_)?;
            for local in state.source_bindings.iter().rev() {
                self.tick()?;
                let type_ = self.instantiate(&local.type_)?;
                let value = self.instantiate(local.value.as_ref().expect("source is a let"))?;
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
            self.txn.lctx = state.saved_lctx.clone();
            return Ok(RecordStep::Complete(term));
        }
        let type_ = self.whnf(&state.constructor.type_)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = type_.node()
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let Some(syntax) = state.fields.remove(binder_name) else {
            // Source order is semantic: the first source providing a field wins.
            // Copied fields remain real constructor arguments; K1 checks any
            // dependency invalidated by a preceding explicit replacement.
            for source in &state.sources {
                match self.record_field(source.clone(), binder_name) {
                    Ok(value) => {
                        let value = self.finish_term(value, Some(binder_type))?;
                        return Ok(RecordStep::Copy {
                            value,
                            codomain: body.clone(),
                        });
                    }
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::RecordTerm(
                        RecordTermError::UnknownField(_),
                    ))) => {}
                    Err(error) => return Err(error),
                }
            }
            return Err(error(RecordTermError::MissingField(binder_name.clone())));
        };
        Ok(RecordStep::Field {
            syntax,
            domain: binder_type.clone(),
            codomain: body.clone(),
        })
    }

    pub(super) fn accept_record_field(
        &mut self,
        state: &mut RecordBuild<'_>,
        codomain: &Expr,
        value: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        state.constructor.type_ = self.substitute(codomain, &value.value)?;
        state.constructor.value = Expr::app(state.constructor.value.clone(), value.value);
        state.remaining -= 1;
        Ok(())
    }
}
