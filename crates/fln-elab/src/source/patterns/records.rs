//! Record patterns retain their written labels until the discriminant has a checked
//! structure type. Inherited fields become ordinary projection lets in the branch;
//! a record label never creates a constructor or an unchecked local.
use super::*;
use crate::records::imported::ImportedStructures;
use fln_env::constants::ConstructorVal;

pub(in crate::source) struct Parts<'a> {
    pub fields: Vec<(Name, &'a Syntax)>,
    pub ellipsis: bool,
    pub annotation: Option<&'a Syntax>,
}

pub(in crate::source) fn parts(
    syntax: &Syntax,
) -> Result<Option<Parts<'_>>, NatDefinitionElabError> {
    if syntax.kind() != Some(&parser_kind(&["Term", "structInst"])) {
        return Ok(None);
    }
    let args = expect_node(
        syntax,
        &parser_kind(&["Term", "structInst"]),
        6,
        "record pattern",
    )?;
    expect_atom(&args[0], "{", "record pattern opener")?;
    expect_atom(&args[5], "}", "record pattern closer")?;
    expect_empty_null(&args[1], "record patterns do not have update sources")?;
    let [tail] = expect_node(
        &args[3],
        &parser_kind(&["Term", "optEllipsis"]),
        1,
        "record ellipsis",
    )?
    else {
        return Err(invalid());
    };
    let ellipsis = match expect_null_args(tail, "record ellipsis")? {
        [] => false,
        [tail] => {
            expect_atom(tail, "..", "record ellipsis")?;
            true
        }
        _ => return Err(invalid()),
    };
    let annotation = match expect_null_args(&args[4], "record pattern annotation")? {
        [] => None,
        [colon, type_] => {
            expect_atom(colon, ":", "record annotation")?;
            Some(type_)
        }
        _ => return Err(invalid()),
    };
    let [rows] = expect_node(
        &args[2],
        &parser_kind(&["Term", "structInstFields"]),
        1,
        "record pattern fields",
    )?
    else {
        return Err(invalid());
    };
    let mut fields = Vec::new();
    let mut seen = HashSet::new();
    for (index, field) in expect_null_args(rows, "record fields")?.iter().enumerate() {
        if index % 2 == 1 {
            if expect_empty_null(field, "record line separator").is_err() {
                expect_atom(field, ",", "record separator")?;
            }
            continue;
        }
        let [label, value] = expect_node(
            field,
            &parser_kind(&["Term", "structInstField"]),
            2,
            "record pattern field",
        )?
        else {
            return Err(invalid());
        };
        let [label, path] = expect_node(
            label,
            &parser_kind(&["Term", "structInstLVal"]),
            2,
            "record field label",
        )?
        else {
            return Err(invalid());
        };
        expect_empty_null(path, "record label path")?;
        let Syntax::Ident { val, .. } = label else {
            return Err(invalid());
        };
        let name = val.erase_macro_scopes();
        if !seen.insert(name.clone()) {
            return Err(field_error(record_terms::RecordTermError::DuplicateField(
                name,
            )));
        }
        let value = match expect_null_args(value, "record field value")? {
            [] => label,
            [binders, annotation, value] => {
                expect_empty_null(binders, "record pattern field binders")?;
                expect_empty_null(annotation, "record pattern field annotation")?;
                let [assignment, private, value] = expect_node(
                    value,
                    &parser_kind(&["Term", "structInstFieldDef"]),
                    3,
                    "record pattern assignment",
                )?
                else {
                    return Err(invalid());
                };
                expect_atom(assignment, ":=", "record pattern assignment")?;
                expect_empty_null(private, "private record pattern")?;
                value
            }
            _ => return Err(invalid()),
        };
        fields.push((name, value));
    }
    Ok(Some(Parts {
        fields,
        ellipsis,
        annotation,
    }))
}

fn field_error(error: record_terms::RecordTermError) -> NatDefinitionElabError {
    failure(SourceInferenceError::RecordTerm(error))
}
fn metadata_error(error: crate::records::RecordError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Record(error))
}

impl Context {
    /// Reuse the constructor-typing model with nested records in physical field
    /// order. Variable collection still used the original, written field order.
    pub(in crate::source) fn record_pattern_model_arguments(
        &mut self,
        fields: &[(Name, &Syntax)],
        paths: &[Vec<Name>],
    ) -> Result<Vec<Syntax>, NatDefinitionElabError> {
        struct Node {
            fields: Vec<(Name, Option<Syntax>, Option<usize>)>,
        }
        let mut nodes = vec![Node { fields: Vec::new() }];
        for ((_, value), path) in fields.iter().zip(paths) {
            let mut node = 0;
            for (depth, label) in path.iter().enumerate() {
                self.tick()?;
                let mut found = None;
                for (index, (name, _, _)) in nodes[node].fields.iter().enumerate() {
                    self.tick()?;
                    if name == label {
                        found = Some(index);
                        break;
                    }
                }
                let index = match found {
                    Some(index) => index,
                    None => {
                        let index = nodes[node].fields.len();
                        nodes[node].fields.push((label.clone(), None, None));
                        index
                    }
                };
                if depth + 1 == path.len() {
                    nodes[node].fields[index].1 = Some(self.copy_pattern_syntax(value)?);
                } else {
                    node = match nodes[node].fields[index].2 {
                        Some(next) => next,
                        None => {
                            let next = nodes.len();
                            nodes.push(Node { fields: Vec::new() });
                            nodes[node].fields[index].2 = Some(next);
                            next
                        }
                    };
                }
            }
        }
        let mut built = HashMap::<usize, Syntax>::new();
        let mut root = Vec::new();
        for (index, node) in nodes.into_iter().enumerate().rev() {
            self.tick()?;
            let mut rows = Vec::new();
            for (label, value, child) in node.fields {
                self.tick()?;
                let value = match (value, child) {
                    (Some(value), None) => value,
                    (None, Some(child)) => built.remove(&child).ok_or_else(invalid)?,
                    _ => return Err(invalid()),
                };
                if index == 0 {
                    root.push(arguments::argument(&Some(label), value));
                } else {
                    if !rows.is_empty() {
                        rows.push(atom(","));
                    }
                    rows.push(Syntax::node(
                        parser_kind(&["Term", "structInstField"]),
                        vec![
                            Syntax::node(
                                parser_kind(&["Term", "structInstLVal"]),
                                vec![identifier(label), null(vec![])],
                            ),
                            null(vec![
                                null(vec![]),
                                null(vec![]),
                                Syntax::node(
                                    parser_kind(&["Term", "structInstFieldDef"]),
                                    vec![atom(":="), null(vec![]), value],
                                ),
                            ]),
                        ],
                    ));
                }
            }
            if index != 0 {
                built.insert(
                    index,
                    Syntax::node(
                        parser_kind(&["Term", "structInst"]),
                        vec![
                            atom("{"),
                            null(vec![]),
                            Syntax::node(
                                parser_kind(&["Term", "structInstFields"]),
                                vec![null(rows)],
                            ),
                            Syntax::node(
                                parser_kind(&["Term", "optEllipsis"]),
                                vec![null(vec![atom("..")])],
                            ),
                            null(vec![]),
                            atom("}"),
                        ],
                    ),
                );
            }
        }
        root.push(ellipsis());
        Ok(root)
    }

    fn pattern_field_family(
        &mut self,
        owner: &Name,
        field: usize,
    ) -> Result<Name, NatDefinitionElabError> {
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(owner) else {
            return Err(invalid());
        };
        let Some(ConstantInfo::Ctor(ctor)) = family
            .ctors
            .first()
            .and_then(|name| self.txn.env.find(name))
        else {
            return Err(invalid());
        };
        let count = ctor.num_params as usize + field;
        let mut type_ = ctor.base.type_.clone();
        for _ in 0..count {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Err(invalid());
            };
            type_ = body.clone();
        }
        let ExprNode::ForallE { binder_type, .. } = type_.node() else {
            return Err(invalid());
        };
        let type_ = self.whnf(binder_type)?;
        let mut head = &type_;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(invalid());
        };
        Ok(name.clone())
    }

    /// Search only physical subobjects recorded by the admitted structure metadata.
    /// Ordinary one-constructor inductives do not acquire record syntax this way.
    fn pattern_field_path(
        &mut self,
        structures: &ImportedStructures,
        root: &Name,
        label: &Name,
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        let components = scope::components(label).map_err(|_| invalid())?;
        let mut owner = root.clone();
        let mut result = Vec::new();
        for (position, component) in components.iter().enumerate() {
            self.tick()?;
            let atomic = Name::from_components([component.as_str()]);
            let mut pending =
                std::collections::VecDeque::from([(owner.clone(), Vec::<Name>::new())]);
            let mut found = None;
            let mut visited = HashSet::new();
            while let Some((record, path)) = pending.pop_front() {
                self.tick()?;
                if !visited.insert(record.clone()) {
                    continue;
                }
                if visited.len() > 256 || path.len() > 256 {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let entry = structures.get(&record).ok_or_else(|| {
                    field_error(record_terms::RecordTermError::ExpectedRecordType)
                })?;
                for (index, field) in entry.fields.iter().enumerate() {
                    self.tick()?;
                    let mut next = path.clone();
                    next.push(field.name.clone());
                    if field.name == atomic {
                        found = Some((record.clone(), index, next));
                        break;
                    }
                    if let Some(parent) = &field.subobject {
                        pending.push_back((parent.clone(), next));
                    }
                }
                if found.is_some() {
                    break;
                }
            }
            let (record, index, path) = found.ok_or_else(|| {
                field_error(record_terms::RecordTermError::UnknownField(label.clone()))
            })?;
            result.extend(path);
            if position + 1 < components.len() {
                owner = self.pattern_field_family(&record, index)?;
            }
        }
        if result.is_empty() {
            return Err(invalid());
        }
        Ok(result)
    }

    pub(in crate::source) fn record_pattern_paths(
        &mut self,
        family: &Name,
        labels: &[Name],
        ellipsis: bool,
    ) -> Result<Vec<Vec<Name>>, NatDefinitionElabError> {
        let structures = ImportedStructures::read(&self.txn.env).map_err(metadata_error)?;
        if structures.get(family).is_none() {
            return Err(field_error(
                record_terms::RecordTermError::ExpectedRecordType,
            ));
        }
        let mut paths = Vec::<Vec<Name>>::new();
        for label in labels {
            self.tick()?;
            let path = self.pattern_field_path(&structures, family, label)?;
            for previous in &paths {
                self.tick()?;
                if previous.starts_with(&path) || path.starts_with(previous) {
                    return Err(field_error(record_terms::RecordTermError::DuplicateField(
                        label.clone(),
                    )));
                }
            }
            paths.push(path);
        }
        if !ellipsis {
            let mut pending = vec![(family.clone(), Vec::<Name>::new())];
            while let Some((owner, prefix)) = pending.pop() {
                self.tick()?;
                if prefix.len() > 256 {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let entry = structures.get(&owner).ok_or_else(invalid)?;
                for (index, field) in entry.fields.iter().enumerate() {
                    self.tick()?;
                    let mut path = prefix.clone();
                    path.push(field.name.clone());
                    let mut supplied = false;
                    let mut nested = false;
                    for candidate in &paths {
                        self.tick()?;
                        supplied |= candidate == &path;
                        nested |= candidate.starts_with(&path);
                    }
                    if supplied {
                        continue;
                    }
                    if let Some(parent) = &field.subobject {
                        pending.push((parent.clone(), path));
                    } else if nested {
                        pending.push((self.pattern_field_family(&owner, index)?, path));
                    } else {
                        return Err(field_error(record_terms::RecordTermError::MissingField(
                            field.name.clone(),
                        )));
                    }
                }
            }
        }
        Ok(paths)
    }

    /// The matrix's labels resolve only here, after the actual family is known.
    pub(in crate::source) fn bind_record_pattern_layout(
        &mut self,
        family: &Name,
        constructor: &ConstructorVal,
        layout: &[Syntax],
        fields: &mut Vec<Option<Name>>,
    ) -> Result<(), NatDefinitionElabError> {
        let (arguments, ellipsis) = application::split_ellipsis(layout)?;
        let mut labels = Vec::new();
        let mut columns = Vec::new();
        for argument in arguments {
            self.tick()?;
            let Some((label, value)) = arguments::named_argument(argument)? else {
                return Err(invalid());
            };
            let column = matching::pattern_name(value)?.ok_or_else(invalid)?;
            if !column.parent().is_anonymous() || !matches!(column.leaf_view(), LeafView::Num(_)) {
                return Err(invalid());
            }
            labels.push(label);
            columns.push(column);
        }
        let paths = self.record_pattern_paths(family, &labels, ellipsis)?;
        let mut cursor = constructor.base.type_.clone();
        let mut telescope = Vec::new();
        while let ExprNode::ForallE {
            binder_name, body, ..
        } = cursor.node()
        {
            self.tick()?;
            if telescope.len() > 512 {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            telescope.push(binder_name.clone());
            cursor = body.clone();
        }
        if telescope.len() != constructor.num_params as usize + constructor.num_fields as usize {
            return Err(invalid());
        }
        if fields.is_empty() {
            fields.resize(telescope.len(), None);
        }
        for (column, path) in columns.into_iter().zip(paths) {
            self.tick()?;
            let mut selected = None;
            for (index, label) in telescope
                .iter()
                .enumerate()
                .skip(constructor.num_params as usize)
            {
                self.tick()?;
                if label == &path[0] {
                    selected = Some(index);
                    break;
                }
            }
            let index = selected.ok_or_else(invalid)?;
            let root = match &fields[index] {
                Some(root) => root.clone(),
                None => {
                    let root = if path.len() == 1 {
                        column.clone()
                    } else {
                        self.matrix_name()?
                    };
                    fields[index] = Some(root.clone());
                    root
                }
            };
            self.matrix_shared_columns.insert(root.clone());
            self.matrix_shared_columns.insert(column.clone());
            if path.len() == 1 {
                if column != root {
                    self.matrix_field_aliases.insert(column, root);
                }
            } else {
                let path = path[1..].to_vec();
                let count = self
                    .matrix_record_projections
                    .get(&root)
                    .map_or(0, Vec::len);
                let mut canonical = None;
                for index in 0..count {
                    self.tick()?;
                    let (name, known) = &self.matrix_record_projections[&root][index];
                    if known == &path {
                        canonical = Some(name.clone());
                        break;
                    }
                }
                if let Some(canonical) = canonical {
                    if canonical != column {
                        self.matrix_field_aliases.insert(column, canonical);
                    }
                } else {
                    self.matrix_record_projections
                        .entry(root)
                        .or_default()
                        .push((column, path));
                }
            }
        }
        Ok(())
    }

    pub(in crate::source) fn bind_record_matrix_projections(
        &mut self,
        locals: &mut Vec<LocalDecl>,
    ) -> Result<(), NatDefinitionElabError> {
        let roots = locals.clone();
        for root in roots {
            self.tick()?;
            let Some(projections) = self.matrix_record_projections.get(&root.user_name).cloned()
            else {
                continue;
            };
            for (name, path) in projections {
                self.tick()?;
                let mut value = Typed {
                    value: Expr::fvar(root.id.clone()),
                    type_: root.type_.clone(),
                };
                for label in path {
                    self.tick()?;
                    value = self.record_field(value, &label)?;
                }
                value.value = self.whnf(&value.value)?;
                let id = FVarId(self.fresh_name()?);
                self.txn
                    .lctx
                    .add_let(id.clone(), name, value.type_, value.value.clone());
                if matches!(value.value.node(), ExprNode::FVar { .. }) {
                    self.matrix_aliases.insert(id.clone(), value.value);
                }
                locals.push(self.txn.lctx.find(&id).ok_or_else(invalid)?.clone());
            }
        }
        Ok(())
    }
}
