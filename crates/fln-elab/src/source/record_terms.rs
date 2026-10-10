//! Named record construction. Field names select constructor arguments, never
//! independent declarations or trusted projections. Elaboration follows the
//! constructor telescope so later field types see the actual earlier values.
use super::*;
use crate::records::RecordBudget;
use crate::records::inheritance::{RecordParents, direct_fields};
use fln_core::name::LeafView;
use fln_env::constants::ConstantInfo;
use std::collections::HashMap;

#[cfg(test)]
mod expected_tests;
#[cfg(test)]
mod lookup_tests;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordTermError {
    ExpectedRecordType,
    UnknownField(Name),
    DuplicateField(Name),
    MissingField(Name),
    /// `e.i` with `i` past the structure's field count (`fields` of them).
    ProjectionIndex {
        index: u64,
        fields: usize,
    },
    /// `e.i` on a type that is not a one-constructor inductive.
    ProjectionNotStructure,
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
            // The pin's messages' first lines (`Lean/Elab/App.lean`, `resolveLValAux`).
            Self::ProjectionIndex { index, fields } => write!(
                f,
                "Invalid projection: Index `{index}` is invalid for this structure; it must be between 1 and {fields}"
            ),
            Self::ProjectionNotStructure => f.write_str(
                "Invalid projection: Projections extract constructor fields for one-constructor inductive types.",
            ),
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
    // Parent subobjects use heap continuations, never recursive elaboration.
    frames: Vec<RecordFrame<'a>>,
}
struct RecordFrame<'a> {
    parents: HashMap<Name, Vec<Name>>,
    return_codomain: Option<Expr>,
    fields: HashMap<Name, &'a Syntax>,
    constructor: Typed,
    remaining: u32,
    expected: Expr,
    sources: Vec<Typed>,
    source_bindings: Vec<LocalDecl>,
    saved_lctx: LocalContext,
    defaults: Vec<Option<Name>>,
    levels: Vec<Level>,
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

pub(super) enum FieldResolution {
    Value(Typed),
    Method {
        function: Typed,
        receiver: Typed,
        base: Name,
    },
}

pub(super) enum FieldReceiver<'a> {
    Syntax(&'a Syntax, Name),
    Elaborated(Typed, Name),
}

/// Field methods are syntax sugar for a checked lambda. A field's result
/// annotation belongs inside that lambda, where its binders are in scope.
pub(super) fn is_field_notation(syntax: &Syntax) -> bool {
    let Syntax::Node { kind, args, .. } = syntax else {
        return false;
    };
    if kind != &parser_kind(&["Term", "structInstField"]) {
        return false;
    }
    let Some(Syntax::Node { args: payload, .. }) = args.get(1) else {
        return false;
    };
    payload
        .iter()
        .take(2)
        .any(|syntax| matches!(syntax, Syntax::Node { args, .. } if !args.is_empty()))
}

fn owned_args(mut syntax: Syntax) -> Result<Vec<Syntax>, NatDefinitionElabError> {
    match &mut syntax {
        Syntax::Node { args, .. } => Ok(std::mem::take(args)),
        _ => Err(failure(SourceInferenceError::Scope)),
    }
}

impl Context {
    /// Part of the ordinary inside-out source expansion. Moving the field body
    /// preserves heap-bounded traversal even when methods contain other records.
    pub(super) fn expand_record_field_node(
        &mut self,
        mut syntax: Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if pattern || !is_field_notation(&syntax) {
            return Ok(syntax);
        }
        self.tick()?;
        let field = expect_node(
            &syntax,
            &parser_kind(&["Term", "structInstField"]),
            2,
            "record field",
        )?;
        let [binders, annotation, definition] = expect_null_args(&field[1], "field value")? else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_null_args(binders, "field method binders")?;
        optional_type_syntax(annotation)?;
        let definition = expect_node(
            definition,
            &parser_kind(&["Term", "structInstFieldDef"]),
            3,
            "field assignment",
        )?;
        expect_atom(&definition[0], ":=", "field assignment token")?;
        expect_empty_null(&definition[1], "unsupported private field value")?;

        let Syntax::Node { args: field, .. } = &mut syntax else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let null = |args: Vec<Syntax>| Syntax::node(Name::from_components(["null"]), args);
        let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
        let payload = std::mem::replace(&mut field[1], null(Vec::new()));
        let [binders, annotation, mut definition]: [Syntax; 3] = owned_args(payload)?
            .try_into()
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let binders = owned_args(binders)?;
        let annotation = owned_args(annotation)?.into_iter().next();
        let Syntax::Node {
            args: definition_args,
            ..
        } = &mut definition
        else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let mut value = std::mem::replace(&mut definition_args[2], null(Vec::new()));
        if let Some(annotation) = annotation {
            let [colon, type_]: [Syntax; 2] = owned_args(annotation)?
                .try_into()
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value = Syntax::node(
                parser_kind(&["Term", "typeAscription"]),
                vec![atom("("), value, colon, null(vec![type_]), atom(")")],
            );
        }
        if !binders.is_empty() {
            value = Syntax::node(
                parser_kind(&["Term", "fun"]),
                vec![
                    atom("fun"),
                    Syntax::node(
                        parser_kind(&["Term", "basicFun"]),
                        vec![null(binders), null(Vec::new()), atom("=>"), value],
                    ),
                ],
            );
        }
        definition_args[2] = value;
        field[1] = null(vec![null(Vec::new()), null(Vec::new()), definition]);
        Ok(syntax)
    }

    pub(super) fn field_application_receiver<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Option<FieldReceiver<'a>>, NatDefinitionElabError> {
        let kind = parser_kind(&["Term", "proj"]);
        if syntax.kind() == Some(&kind) {
            let parts = expect_node(syntax, &kind, 3, "field projection")?;
            expect_atom(&parts[1], ".", "field dot")?;
            return Ok(Some(FieldReceiver::Syntax(
                &parts[0],
                projection_field(&parts[2])?,
            )));
        }
        if let Syntax::Ident { val: name, .. } = syntax
            && let Some((receiver, path)) = self.qualified_field_receiver(name)?
        {
            return Ok(Some(FieldReceiver::Elaborated(receiver, path)));
        }
        Ok(None)
    }
    /// Resolve a qualified identifier only after exact local/global lookup has
    /// failed. Names are split structurally: an escaped dot is never a separator.
    pub(super) fn qualified_record_field(
        &mut self,
        name: &Name,
        expected: Option<&Expr>,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let Some((receiver, path)) = self.qualified_field_receiver(name)? else {
            return Ok(None);
        };
        let field = self.resolve_field_path(receiver, &path, false)?;
        Ok(Some(self.field_value(field, expected)?))
    }

    /// Splitting is reserved for identifiers that did not resolve as a whole.
    /// This preserves exact constants, local shadowing and escaped components.
    pub(super) fn qualified_field_receiver(
        &mut self,
        name: &Name,
    ) -> Result<Option<(Typed, Name)>, NatDefinitionElabError> {
        if self.txn.lctx.find_by_user_name(name).is_some()
            || self.resolve_source_name(name)?.is_some()
        {
            return Ok(None);
        }
        let mut prefix = name.clone();
        let mut suffix = Vec::new();
        while !prefix.is_anonymous() {
            self.tick()?;
            let LeafView::Str(part) = prefix.leaf_view() else {
                return Ok(None);
            };
            suffix.push(Name::from_components([part]));
            prefix = prefix.parent().clone();
            // An unqualified name has no receiver prefix. Anonymous internal
            // locals are scope slots, not a namespace or an implicit record.
            if prefix.is_anonymous() {
                break;
            }
            let receiver = if let Some(local) = self
                .txn
                .lctx
                .decls()
                .iter()
                .rev()
                .find(|local| local.user_name == prefix)
            {
                Some(Typed {
                    value: self
                        .matrix_aliases
                        .get(&local.id)
                        .cloned()
                        .unwrap_or_else(|| Expr::fvar(local.id.clone())),
                    type_: local.type_.clone(),
                })
            } else if let Some(resolved) = self.resolve_source_name(&prefix)?
                && self.txn.env.contains(&resolved)
            {
                Some(self.constant(&resolved)?)
            } else {
                None
            };
            if let Some(receiver) = receiver {
                let type_ = self.whnf(&receiver.type_)?;
                if matches!(type_.node(), ExprNode::Sort { .. }) {
                    // A namespace prefix such as Nat is not a receiver.
                    return Ok(None);
                }
                let path = suffix
                    .iter()
                    .rev()
                    .fold(Name::anonymous(), |path, part| path.append_core(part));
                return Ok(Some((receiver, path)));
            }
        }
        Ok(None)
    }

    pub(super) fn resolve_field_path(
        &mut self,
        mut receiver: Typed,
        path: &Name,
        has_arguments: bool,
    ) -> Result<FieldResolution, NatDefinitionElabError> {
        if let LeafView::Num(index) = path.leaf_view()
            && path.parent().is_anonymous()
        {
            let field = self.indexed_field(receiver.clone(), index)?;
            return self.resolve_field(receiver, &field, has_arguments);
        }
        let parts = scope::components(path).map_err(|_| failure(SourceInferenceError::Scope))?;
        let Some((last, prefix)) = parts.split_last() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        for part in prefix {
            self.tick()?;
            let field =
                self.resolve_field(receiver, &Name::from_components([part.as_str()]), false)?;
            receiver = self.field_value(field, None)?;
        }
        self.resolve_field(
            receiver,
            &Name::from_components([last.as_str()]),
            has_arguments,
        )
    }

    /// Real fields retain priority over methods. A failed candidate cannot
    /// leak implicit assignments or instance choices into a method lookup.
    /// Non-lookup errors, including resource stops, are never swallowed.
    fn resolve_field(
        &mut self,
        mut receiver: Typed,
        field: &Name,
        has_arguments: bool,
    ) -> Result<FieldResolution, NatDefinitionElabError> {
        self.flush(false)?;
        self.resolve_instances(false)?;
        loop {
            self.tick()?;
            // Inserted dictionaries may determine the receiver type through
            // their projections; inspect its head only after resolving them.
            self.resolve_instances(false)?;
            receiver.type_ =
                self.whnf_with_transparency(&receiver.type_, UnificationTransparency::None, true)?;
            if let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = receiver.type_.node()
                && (*binder_info == BinderInfo::Implicit
                    || *binder_info == BinderInfo::InstImplicit
                    || has_arguments && *binder_info == BinderInfo::StrictImplicit)
            {
                let argument = if *binder_info == BinderInfo::InstImplicit {
                    self.instance_hole(binder_type.clone())?
                } else {
                    self.hole(binder_type.clone())?
                };
                receiver.type_ = self.substitute(body, &argument)?;
                receiver.value = Expr::app(receiver.value, argument);
                continue;
            }
            let mut head = &receiver.type_;
            let mut arguments = Vec::new();
            while let ExprNode::App { f, a } = head.node() {
                self.tick()?;
                arguments.push(a.clone());
                head = f;
            }
            let base = match head.node() {
                ExprNode::MVar { .. } => {
                    // The pin defaults unresolved receiver types here (for
                    // example `(2).succ` and `(1.5).abs`) without demanding
                    // that unrelated synthetic goals are already solvable.
                    self.resolve_instances_with_defaults()?;
                    let instantiated = self.instantiate(&receiver.type_)?;
                    if instantiated == receiver.type_ {
                        return Err(error(RecordTermError::ExpectedRecordType));
                    }
                    receiver.type_ = instantiated;
                    continue;
                }
                ExprNode::Const { name, .. } => name.clone(),
                ExprNode::ForallE { .. } => Name::from_components(["Function"]),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    // Reduce the dictionary/record supplying a type field,
                    // preserving the projected field's own alias namespace.
                    let value = self.whnf(expr)?;
                    if &value == expr {
                        return Err(error(RecordTermError::ExpectedRecordType));
                    }
                    let mut projected = Expr::proj(struct_name.clone(), *idx, value);
                    for argument in arguments.into_iter().rev() {
                        self.tick()?;
                        projected = Expr::app(projected, argument);
                    }
                    receiver.type_ = projected;
                    continue;
                }
                _ => return Err(error(RecordTermError::ExpectedRecordType)),
            };
            let definition = self.txn.env.find(&base).cloned();
            let mut missing = error(RecordTermError::UnknownField(field.clone()));
            if matches!(definition, Some(ConstantInfo::Induct(_))) {
                let mut trial = self.clone();
                let projected = trial.record_field(receiver.clone(), field);
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                match projected {
                    Ok(value) => {
                        *self = trial;
                        return Ok(FieldResolution::Value(value));
                    }
                    Err(
                        reason @ NatDefinitionElabError::Inference(
                            SourceInferenceError::RecordTerm(
                                RecordTermError::ExpectedRecordType
                                | RecordTermError::UnknownField(_),
                            ),
                        ),
                    ) => missing = reason,
                    Err(reason) => return Err(reason),
                }
            }
            let method = base.append_core(field);
            // `l.size` inside `T.size`'s own body is a recursive call: after a structure
            // field and before the environment, the pin searches the local context for the
            // declaration being defined (`LValResolution.localRec`,
            // `Lean/Elab/App.lean:1557`).
            if let Some(recursion) = &self.recursion
                && recursion.name == method
            {
                return Ok(FieldResolution::Method {
                    function: recursion.reference.clone(),
                    receiver,
                    base,
                });
            }
            // Before the recursion context exists, a reference to the declaration being
            // defined is reported as the unknown constant it still is, exactly as a direct
            // `T.size l` is: `definition_body` retries such a failure with the structural
            // recursion context, where the branch above resolves it.
            if self.recursion.is_none()
                && self.defining.as_ref() == Some(&method)
                && !self.txn.env.contains(&method)
            {
                return Err(failure(SourceInferenceError::UnknownConstant(method)));
            }
            // An alias owns its method namespace. Only a failed lookup
            // unfolds one definition, so intermediate aliases are not skipped
            // in favor of a field on the final underlying structure.
            if self.txn.env.contains(&method) {
                return Ok(FieldResolution::Method {
                    function: self.constant(&method)?,
                    receiver,
                    base,
                });
            }
            let Some(ConstantInfo::Defn(definition)) = definition else {
                return Err(missing);
            };
            if definition.safety != DefinitionSafety::Safe {
                return Err(missing);
            }
            let ExprNode::Const { levels, .. } = head.node() else {
                return Err(missing);
            };
            let mut unfolded =
                self.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
            for argument in arguments.into_iter().rev() {
                self.tick()?;
                unfolded = Expr::app(unfolded, argument);
            }
            receiver.type_ = unfolded;
        }
    }

    fn field_value(
        &mut self,
        field: FieldResolution,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let FieldResolution::Method {
            function,
            receiver,
            base,
        } = field
        else {
            let FieldResolution::Value(value) = field else {
                unreachable!()
            };
            return Ok(value);
        };
        // A bare qualified method still applies its receiver. Preserve the
        // whole term's expectation here, just as the explicit projection and
        // application paths do, so its implicit result constructor is chosen
        // before instance synthesis. Intermediate path receivers have no such
        // expectation: it belongs only to the final field or method.
        let mut state =
            self.start_field_application(function, receiver, &base, &[], expected.cloned(), false)?;
        while let Some(argument) = self.next_named_argument(&mut state)? {
            let application::ApplicationValue::Elaborated(value) = argument.value else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let value = self.finish_term(value, Some(&argument.domain))?;
            self.constrain_type(&value.type_, &argument.domain)?;
            self.add_named_argument(&mut state, &argument.codomain, value)?;
        }
        self.finish_named_application(state)
    }

    /// Apply admitted generated projections to the actual receiver. In
    /// particular, an instance-implicit class receiver must not be replaced by
    /// a dictionary selected from the surrounding context.
    /// `e.i` (`fieldIdx`): the name of the `i`-th field, from one, of the structure
    /// `e`'s type (`LValResolution.projIdx`, `Lean/Elab/App.lean`).
    fn indexed_field(
        &mut self,
        receiver: Typed,
        index: u64,
    ) -> Result<Name, NatDefinitionElabError> {
        let receiver = self.insert_implicits(receiver, ImplicitInsertion::FieldReceiver)?;
        let target = self.whnf(&receiver.type_)?;
        let mut head = &target;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(error(RecordTermError::ProjectionNotStructure));
        };
        let mut remaining = RecordBudget::default().max_nodes;
        let fields = direct_fields(&self.txn.env, name, &mut remaining)
            .map_err(|_| error(RecordTermError::ProjectionNotStructure))?;
        let position = usize::try_from(index)
            .ok()
            .and_then(|index| index.checked_sub(1))
            .and_then(|index| fields.get(index));
        position.map(|(label, _)| label.clone()).ok_or_else(|| {
            error(RecordTermError::ProjectionIndex {
                index,
                fields: fields.len(),
            })
        })
    }

    pub(super) fn record_field(
        &mut self,
        receiver: Typed,
        field: &Name,
    ) -> Result<Typed, NatDefinitionElabError> {
        let receiver = self.insert_implicits(receiver, ImplicitInsertion::FieldReceiver)?;
        match self.physical_record_field(receiver.clone(), field) {
            Err(NatDefinitionElabError::Inference(SourceInferenceError::RecordTerm(
                RecordTermError::UnknownField(_),
            ))) => {}
            result => return result,
        }
        let target = self.whnf(&receiver.type_)?;
        let mut head = &target;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(error(RecordTermError::ExpectedRecordType));
        };
        let registry = RecordParents::read(&self.txn.env)
            .map_err(|e| failure(SourceInferenceError::Record(e)))?;
        let path = registry
            .fields(&self.txn.env, name, RecordBudget::default())
            .map_err(|e| failure(SourceInferenceError::Record(e)))?
            .into_iter()
            .find(|row| &row.name == field)
            .ok_or_else(|| error(RecordTermError::UnknownField(field.clone())))?;
        let mut receiver = receiver;
        let mut remaining = RecordBudget::default().max_nodes;
        for (owner, index) in path.path {
            self.tick()?;
            let fields = direct_fields(&self.txn.env, &owner, &mut remaining)
                .map_err(|e| failure(SourceInferenceError::Record(e)))?;
            let (label, _) = fields
                .get(index as usize)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            receiver = self.physical_record_field(receiver, label)?;
        }
        Ok(receiver)
    }

    fn physical_record_field(
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
        let projection = match self.txn.env.find(&projection_name).cloned() {
            Some(ConstantInfo::Defn(projection)) if projection.safety == DefinitionSafety::Safe => {
                projection.base
            }
            Some(ConstantInfo::Thm(projection)) => projection.base,
            _ => return Err(error(RecordTermError::UnknownField(field.clone()))),
        };
        if projection.level_params.len() != levels.len() {
            return Err(error(RecordTermError::UnknownField(field.clone())));
        }
        let mut term = Typed {
            value: Expr::const_(projection_name, levels.clone()),
            type_: self.instantiate_params(&projection.type_, &projection.level_params, levels)?,
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
                // `sepByIndent … (allowTrailingSep := true)`: a `,`, or a line break, which is
                // the pin's empty separator node.
                if expect_empty_null(syntax, "record line separator").is_err() {
                    expect_atom(syntax, ",", "record field separator")?;
                }
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
        Ok(RecordBuild {
            frames: vec![self.start_record_frame(parts, expected, sources)?],
        })
    }

    fn start_record_frame<'a>(
        &mut self,
        parts: RecordParts<'a>,
        expected: Option<Expr>,
        sources: Vec<Typed>,
    ) -> Result<RecordFrame<'a>, NatDefinitionElabError> {
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
        let inherited = RecordParents::read(&self.txn.env)
            .map_err(|e| failure(SourceInferenceError::Record(e)))?;
        let mut parents = HashMap::new();
        let mut remaining = RecordBudget::default().max_nodes;
        let physical = direct_fields(&self.txn.env, name, &mut remaining)
            .map_err(|e| failure(SourceInferenceError::Record(e)))?;
        for parent in inherited.parents(name) {
            self.tick()?;
            let (label, _) = physical
                .get(parent.field as usize)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let fields = inherited
                .fields(&self.txn.env, &parent.parent, RecordBudget::default())
                .map_err(|e| failure(SourceInferenceError::Record(e)))?;
            let labels: Vec<_> = fields.into_iter().map(|field| field.name).collect();
            for inherited_label in &labels {
                self.tick()?;
                if !known.insert(inherited_label.clone()) {
                    return Err(error(RecordTermError::DuplicateField(
                        inherited_label.clone(),
                    )));
                }
            }
            // Supplying both a parent object and one of its flattened fields is
            // ambiguous in this profile, never an excuse to discard a value.
            if parts.fields.iter().any(|(field, _)| field == label)
                && parts.fields.iter().any(|(field, _)| labels.contains(field))
            {
                return Err(error(RecordTermError::DuplicateField(label.clone())));
            }
            parents.insert(label.clone(), labels);
        }
        for (label, _) in &parts.fields {
            if !known.contains(label) {
                return Err(error(RecordTermError::UnknownField(label.clone())));
            }
        }
        let registry = crate::records::defaults::RecordDefaults::read(&self.txn.env)
            .map_err(|e| failure(SourceInferenceError::Record(e)))?;
        let defaults = (0..ctor.num_fields)
            .map(|field| registry.helper(name, field).cloned())
            .collect();
        let levels = levels.clone();
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
        Ok(RecordFrame {
            parents,
            return_codomain: None,
            fields: parts.fields.into_iter().collect(),
            constructor,
            remaining: ctor.num_fields,
            expected,
            sources: bound_sources,
            source_bindings,
            saved_lctx,
            defaults,
            levels,
        })
    }

    pub(super) fn next_record_field<'a>(
        &mut self,
        state: &mut RecordBuild<'a>,
    ) -> Result<RecordStep<'a>, NatDefinitionElabError> {
        loop {
            self.tick()?;
            let frame = state
                .frames
                .last_mut()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let mut parent = None;
            if frame.remaining != 0 {
                let type_ = self.whnf(&frame.constructor.type_)?;
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = type_.node()
                else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                if let Some(labels) = frame.parents.get(binder_name).cloned() {
                    parent = Some((labels, binder_type.clone(), body.clone(), *binder_info));
                }
            }
            let explicit_inherited = parent.as_ref().is_some_and(|(labels, _, _, _)| {
                labels.iter().any(|label| frame.fields.contains_key(label))
            });
            if !explicit_inherited {
                match self.next_physical_record_field(frame) {
                    Ok(RecordStep::Complete(term)) => {
                        let finished = state
                            .frames
                            .pop()
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                        let Some(codomain) = finished.return_codomain else {
                            return Ok(RecordStep::Complete(term));
                        };
                        self.accept_record_field(state, &codomain, term)?;
                        continue;
                    }
                    // Copy a whole available parent before considering defaults:
                    // reconstructing it unnecessarily can change dependent types.
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::RecordTerm(
                        RecordTermError::MissingField(_),
                    ))) if parent.is_some() => {}
                    result => return result,
                }
            }
            let (labels, domain, codomain, style) =
                parent.ok_or_else(|| failure(SourceInferenceError::Scope))?;
            if !explicit_inherited && style == BinderInfo::InstImplicit {
                // Omitted class parents may use an available dictionary. Probe
                // transactionally so a failed search cannot constrain a later
                // structural initializer or refund the work it already spent.
                let mut trial = self.clone();
                let attempt = (|| {
                    trial.flush(false)?;
                    let registry = crate::instances::InstanceRegistry::read_with_scopes(
                        &trial.txn.env,
                        &trial.source_scope.instance_scopes,
                    )
                    .map_err(instances::registry_error)?;
                    let saved = trial.txn.lctx.clone();
                    let suspended = std::mem::take(&mut trial.equations);
                    let hole = trial.instance_hole(domain.clone())?;
                    let ExprNode::MVar { id } = hole.node() else {
                        unreachable!("fresh parent instance hole");
                    };
                    // Pinned StructInst.trySynthParent uses trySynthInstance:
                    // a missing optional parent dictionary permits structural
                    // defaults. It is not a required synthetic instance goal,
                    // whose concrete failure resolve_instances must report.
                    if trial.search_instance(id.clone(), &registry)?
                        != instances::SearchResult::Solved
                    {
                        return Ok(None);
                    }
                    trial.txn.lctx = saved;
                    trial.equations.extend(suspended);
                    let value = trial.instantiate(&hole)?;
                    Ok::<_, NatDefinitionElabError>(
                        (!value.has_expr_mvar() && !value.has_level_mvar()).then_some(Typed {
                            value,
                            type_: domain.clone(),
                        }),
                    )
                })();
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                if let Some(value) = attempt? {
                    *self = trial;
                    return Ok(RecordStep::Copy { value, codomain });
                }
            }
            let frame = state.frames.last_mut().expect("active record frame");
            let mut fields = Vec::new();
            for label in labels {
                self.tick()?;
                if let Some(syntax) = frame.fields.remove(&label) {
                    fields.push((label, syntax));
                }
            }
            let sources = frame.sources.clone();
            if state.frames.len() >= RecordBudget::default().max_binders {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            let mut child = self.start_record_frame(
                RecordParts {
                    fields,
                    annotation: None,
                    sources: Vec::new(),
                },
                Some(domain),
                sources,
            )?;
            child.return_codomain = Some(codomain);
            state.frames.push(child);
        }
    }

    fn next_physical_record_field<'a>(
        &mut self,
        state: &mut RecordFrame<'a>,
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
            let index = state
                .defaults
                .len()
                .checked_sub(state.remaining as usize)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            if let Some(helper) = &state.defaults[index] {
                let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(helper).cloned()
                else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                let mut value = Typed {
                    // The pin's instantiateStructDefaultValueFn? instantiates
                    // the registered helper's checked body, rather than leaving
                    // an application of its semireducible name. Later fields
                    // must see the actual chosen value at their expected type,
                    // without changing ordinary instance-search transparency.
                    value: self.instantiate_params(
                        &definition.value,
                        &definition.base.level_params,
                        &state.levels,
                    )?,
                    type_: self.instantiate_params(
                        &definition.base.type_,
                        &definition.base.level_params,
                        &state.levels,
                    )?,
                };
                // Explicitly supply the actual parameters and preceding values,
                // including instance parameters. Never re-search a dictionary.
                let mut arguments = Vec::new();
                let mut head = &state.constructor.value;
                while let ExprNode::App { f, a } = head.node() {
                    self.tick()?;
                    arguments.push(a.clone());
                    head = f;
                }
                for argument in arguments.into_iter().rev() {
                    self.tick()?;
                    let type_ = self.whnf(&value.type_)?;
                    let ExprNode::ForallE { body, .. } = type_.node() else {
                        return Err(failure(SourceInferenceError::Scope));
                    };
                    value.type_ = self.substitute(body, &argument)?;
                    let ExprNode::Lam { body, .. } = value.value.node() else {
                        return Err(failure(SourceInferenceError::Scope));
                    };
                    value.value = self.substitute(body, &argument)?;
                }
                let value = self.finish_term(value, Some(binder_type))?;
                return Ok(RecordStep::Copy {
                    value,
                    codomain: body.clone(),
                });
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
        let state = state
            .frames
            .last_mut()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        state.constructor.type_ = self.substitute(codomain, &value.value)?;
        state.constructor.value = Expr::app(state.constructor.value.clone(), value.value);
        state.remaining -= 1;
        Ok(())
    }
}

/// A projection's field: an identifier, or a `fieldIdx` numeral read as `Name::num`.
pub(super) fn projection_field(syntax: &Syntax) -> Result<Name, NatDefinitionElabError> {
    match syntax {
        Syntax::Ident { val, .. } => Ok(val.clone()),
        Syntax::Node { kind, args, .. }
            if kind == &Name::str(Name::anonymous(), "fieldIdx") && args.len() == 1 =>
        {
            let Syntax::Atom { val, .. } = &args[0] else {
                return Err(failure(SourceInferenceError::Scope));
            };
            val.parse::<u64>()
                .ok()
                .filter(|index| *index > 0)
                .map(|index| Name::num(Name::anonymous(), index))
                .ok_or_else(|| failure(SourceInferenceError::Scope))
        }
        _ => Err(failure(SourceInferenceError::Scope)),
    }
}
