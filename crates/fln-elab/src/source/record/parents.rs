//! Elaborate parent subobjects, copied parents and aliases in the declaration's scope.
//! Aliases are eliminated before constructor/default generation; only physical
//! parent fields enter the record telescope. No declaration is admitted here.
//!
//! A parent whose fields overlap the ones already present is *copied*, as the pin's
//! `withStruct` copies it (vendored `Lean/Elab/Structure.lean:640-835`): each of its fields is
//! reused when present (after a definitional-equality check of its type), and otherwise
//! becomes a field of the record; a parent of the copied parent that overlaps nothing becomes
//! a subobject of the record. The copied parent itself is the `let` alias `toC := C.mk …` of
//! those fields, and its projection `D.toC` is a definition built from them
//! ([`CopiedParent`]).
use super::*;
mod coercions;
use crate::records::RecordError;
use crate::records::inheritance::{RecordParent, RecordParents, direct_fields};
use fln_core::name::LeafView;
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;

/// A parent represented by its fields rather than a subobject: its projection `D.toC` is the
/// definition `fun self => C.mk params …` over the record's fields.
pub(super) struct CopiedParent {
    pub parent: Name,
    /// The projection's last component, `toC`.
    pub label: Name,
    /// The parent's type and its value, over the record's parameters, fields and aliases.
    pub type_: Expr,
    pub value: Expr,
}

/// A copied field's default, the copied parent's: its helper applied to that parent's
/// parameters and the values of its fields before this one, over the record's.
pub(super) struct InheritedDefault {
    pub field: FVarId,
    pub value: Expr,
}

pub(super) struct Inheritance {
    pub fields: Vec<LocalDecl>,
    pub aliases: Vec<LocalDecl>,
    pub parents: Vec<RecordParent>,
    pub copied: Vec<CopiedParent>,
    /// The `extends` clause's parents in order, each with its projection's last component and
    /// whether it is a subobject; `parents` also holds a copied parent's promoted ancestors.
    pub direct: Vec<(Name, Name, bool)>,
    pub defaults: Vec<InheritedDefault>,
    pub labels: HashSet<Name>,
    pub level: Level,
}

fn record_error(error: RecordError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Record(error))
}

impl Context {
    pub(super) fn expand_record_aliases(
        &mut self,
        mut expression: Expr,
        aliases: &[LocalDecl],
    ) -> Result<Expr, NatDefinitionElabError> {
        for alias in aliases.iter().rev() {
            self.tick()?;
            let value = alias
                .value
                .as_ref()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            expression = expression
                .abstract_fvar(&alias.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            expression = self.substitute(&expression, value)?;
        }
        Ok(expression)
    }

    pub(super) fn record_parents(
        &mut self,
        syntax: &Syntax,
        record: &Name,
        is_class: bool,
        budget: RecordBudget,
    ) -> Result<Inheritance, NatDefinitionElabError> {
        let mut result = Inheritance {
            fields: Vec::new(),
            aliases: Vec::new(),
            parents: Vec::new(),
            copied: Vec::new(),
            direct: Vec::new(),
            defaults: Vec::new(),
            labels: HashSet::new(),
            level: Level::one(),
        };
        let syntax = match expect_null_args(syntax, "optional parent clause")? {
            [] => return Ok(result),
            [syntax] => syntax,
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        let parts = expect_node(
            syntax,
            &parser_kind(&["Command", "extends"]),
            3,
            "parent clause",
        )?;
        expect_atom(&parts[0], "extends", "parent keyword")?;
        expect_empty_null(&parts[2], "result sort precedes extends")?;
        let rows = expect_null_args(&parts[1], "parent list")?;
        if rows.is_empty() || rows.len() % 2 == 0 {
            return Err(failure(SourceInferenceError::Scope));
        }
        let registry = RecordParents::read(&self.txn.env).map_err(record_error)?;
        let classes = self.instance_registry()?;
        let mut parent_names = HashSet::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(row, ",", "parent separator")?;
                continue;
            }
            let parts = expect_node(
                row,
                &parser_kind(&["Command", "structParent"]),
                2,
                "parent type",
            )?;
            let type_ = self.type_term(&parts[1])?;
            let type_ = self.expand_record_aliases(type_, &result.aliases)?;
            let type_ = self.whnf(&type_)?;
            let name = record_family(self, &type_)?;
            if !parent_names.insert(name.clone()) {
                return Err(record_error(RecordError::DuplicateField));
            }
            let label = match expect_null_args(&parts[0], "optional parent projection name")? {
                [] => {
                    let LeafView::Str(leaf) = name.leaf_view() else {
                        return Err(record_error(RecordError::InvalidName));
                    };
                    Name::str(Name::anonymous(), format!("to{leaf}"))
                }
                [Syntax::Ident { val, .. }, colon] => {
                    expect_atom(colon, ":", "parent projection colon")?;
                    val.clone()
                }
                _ => return Err(failure(SourceInferenceError::Scope)),
            };
            if label.is_anonymous() || !label.parent().is_anonymous() {
                return Err(record_error(RecordError::InvalidName));
            }
            if !result.labels.insert(label.clone()) {
                return Err(record_error(RecordError::DuplicateField));
            }
            let sort = self
                .known_type(&type_)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            // `extends Inhabited α` under `α : Type _` keeps the parameter's universe hole;
            // the record generalizes it with its own telescope.
            let completed = self.finish_open_universes(Typed {
                value: type_,
                type_: sort,
            })?;
            let level = self.sort_level(&completed)?;
            result.level = Level::max(result.level, level)
                .map_err(|_| record_error(RecordError::ResourceLimit))?;
            let fields = registry
                .fields(&self.txn.env, &name, budget)
                .map_err(record_error)?;
            // `withStruct`: an overlapping parent, or one with no fields after some, is copied.
            if fields
                .iter()
                .any(|field| result.labels.contains(&field.name))
                || (fields.is_empty() && !result.fields.is_empty())
            {
                let value =
                    self.copy_parent(&completed.value, record, &registry, budget, &mut result)?;
                let id = FVarId(self.fresh_name()?);
                let alias = self
                    .txn
                    .lctx
                    .add_let(id, label.clone(), completed.value.clone(), value.clone())
                    .clone();
                result.aliases.push(alias);
                result.direct.push((name.clone(), label.clone(), false));
                result.copied.push(CopiedParent {
                    parent: name,
                    label,
                    type_: completed.value,
                    value,
                });
                if self.txn.lctx.len() > budget.max_binders {
                    return Err(record_error(RecordError::ResourceLimit));
                }
                continue;
            }
            let style = if is_class && classes.is_class(&name) {
                BinderInfo::InstImplicit
            } else {
                BinderInfo::Default
            };
            result.direct.push((name.clone(), label.clone(), true));
            self.add_subobject(
                record,
                &name,
                label,
                completed.value,
                style,
                fields,
                budget,
                &mut result,
            )?;
        }
        Ok(result)
    }

    /// A parent represented by a constructor field of the record (`toB : B`), with an alias for
    /// each of its fields.
    #[allow(clippy::too_many_arguments)]
    fn add_subobject(
        &mut self,
        record: &Name,
        parent: &Name,
        label: Name,
        type_: Expr,
        style: BinderInfo,
        fields: Vec<crate::records::inheritance::FieldPath>,
        budget: RecordBudget,
        result: &mut Inheritance,
    ) -> Result<Expr, NatDefinitionElabError> {
        let id = FVarId(self.fresh_name()?);
        let local = self
            .txn
            .lctx
            .add_param(id.clone(), label, type_.clone(), style)
            .clone();
        result.parents.push(RecordParent {
            record: record.clone(),
            field: result.fields.len() as u32,
            parent: parent.clone(),
        });
        result.fields.push(local);
        let receiver = Typed {
            value: Expr::fvar(id.clone()),
            type_,
        };
        for field in fields {
            self.tick()?;
            if !result.labels.insert(field.name.clone()) {
                return Err(record_error(RecordError::DuplicateField));
            }
            let value = self.record_field(receiver.clone(), &field.name)?;
            let id = FVarId(self.fresh_name()?);
            let alias = self
                .txn
                .lctx
                .add_let(id, field.name, value.type_, value.value)
                .clone();
            result.aliases.push(alias);
            if self.txn.lctx.len() > budget.max_binders {
                return Err(record_error(RecordError::ResourceLimit));
            }
        }
        if self.txn.lctx.len() > budget.max_binders {
            return Err(record_error(RecordError::ResourceLimit));
        }
        Ok(Expr::fvar(id))
    }

    /// `withStructFields` with no subobject: the copied parent `C params`, its fields reused or
    /// added, and its value `C.mk params v₁ … vₙ` over them.
    fn copy_parent(
        &mut self,
        type_: &Expr,
        record: &Name,
        registry: &RecordParents,
        budget: RecordBudget,
        result: &mut Inheritance,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        let type_ = self.whnf(type_)?;
        let (head, arguments) = super::super::operators::spine(&type_);
        let ExprNode::Const {
            name: parent,
            levels,
        } = head.node()
        else {
            return Err(record_error(RecordError::InvalidTelescope));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(parent).cloned() else {
            return Err(record_error(RecordError::InvalidTelescope));
        };
        let [constructor] = family.ctors.as_slice() else {
            return Err(record_error(RecordError::InvalidTelescope));
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(constructor).cloned() else {
            return Err(record_error(RecordError::InvalidTelescope));
        };
        let mut remaining = budget.max_nodes;
        let fields = direct_fields(&self.txn.env, parent, &mut remaining).map_err(record_error)?;
        let styles = constructor_field_styles(&ctor.base.type_, ctor.num_params as usize);
        let subobjects: Vec<(u32, Name)> = registry
            .parents(parent)
            .iter()
            .map(|row| (row.field, row.parent.clone()))
            .collect();
        let defaults =
            crate::records::defaults::RecordDefaults::read(&self.txn.env).map_err(record_error)?;
        let mut values = Vec::new();
        for (index, (field, domain)) in fields.into_iter().enumerate() {
            self.tick()?;
            let domain = self.instantiate_params(&domain, &ctor.base.level_params, levels)?;
            let field_type = domain
                .subst_loose(
                    0,
                    &arguments
                        .iter()
                        .cloned()
                        .chain(values.iter().cloned())
                        .collect::<Vec<_>>(),
                )
                .map_err(|_| record_error(RecordError::InvalidTelescope))?;
            // A field's type reads the record's fields, never its aliases.
            let field_type = self.expand_record_aliases(field_type, &result.aliases)?;
            let subobject = subobjects
                .iter()
                .find(|(at, _)| *at as usize == index)
                .map(|(_, parent)| parent.clone());
            let default = u32::try_from(index)
                .ok()
                .and_then(|index| defaults.helper(parent, index))
                .cloned();
            let value = if result.labels.contains(&field) {
                // A field (or a parent's own parent) already present is reused at its type. Its
                // default stays the earlier parent's, as at the pin; where that has none the pin
                // takes this parent's, which is not carried here, so an instance omitting the
                // field is refused for a missing field rather than given another value.
                let existing = self
                    .txn
                    .lctx
                    .find_by_user_name(&field)
                    .cloned()
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                if !self.defeq_guarded(&existing.type_, &field_type)? {
                    return Err(record_error(RecordError::ParentFieldMismatch));
                }
                Expr::fvar(existing.id)
            } else if let Some(grandparent) = subobject {
                // `withStruct` for the copied parent's parent: copied again when it overlaps,
                // a subobject of the record otherwise.
                let nested = registry
                    .fields(&self.txn.env, &grandparent, budget)
                    .map_err(record_error)?;
                result.labels.insert(field.clone());
                if nested.iter().any(|leaf| result.labels.contains(&leaf.name))
                    || (nested.is_empty() && !result.fields.is_empty())
                {
                    let value = self.copy_parent(&field_type, record, registry, budget, result)?;
                    let id = FVarId(self.fresh_name()?);
                    let alias = self
                        .txn
                        .lctx
                        .add_let(id.clone(), field, field_type, value)
                        .clone();
                    result.aliases.push(alias);
                    Expr::fvar(id)
                } else {
                    let style = styles.get(index).copied().unwrap_or(BinderInfo::Default);
                    self.add_subobject(
                        record,
                        &grandparent,
                        field,
                        field_type,
                        style,
                        nested,
                        budget,
                        result,
                    )?
                }
            } else {
                result.labels.insert(field.clone());
                let id = FVarId(self.fresh_name()?);
                let style = styles.get(index).copied().unwrap_or(BinderInfo::Default);
                let local = self
                    .txn
                    .lctx
                    .add_param(id.clone(), field, field_type, style)
                    .clone();
                result.fields.push(local);
                if let Some(helper) = default {
                    let value = arguments
                        .iter()
                        .cloned()
                        .chain(values.iter().cloned())
                        .fold(Expr::const_(helper, levels.clone()), Expr::app);
                    result.defaults.push(InheritedDefault {
                        field: id.clone(),
                        value,
                    });
                }
                Expr::fvar(id)
            };
            if self.txn.lctx.len() > budget.max_binders {
                return Err(record_error(RecordError::ResourceLimit));
            }
            values.push(value);
        }
        Ok(arguments
            .into_iter()
            .chain(values)
            .fold(Expr::const_(constructor.clone(), levels.clone()), Expr::app))
    }
}

/// The record family a parent type names: a nonrecursive single-constructor family applied
/// to all of its parameters.
fn record_family(context: &mut Context, type_: &Expr) -> Result<Name, NatDefinitionElabError> {
    let mut head = type_;
    let mut arity = 0usize;
    while let ExprNode::App { f, .. } = head.node() {
        context.tick()?;
        arity += 1;
        head = f;
    }
    let ExprNode::Const { name, levels } = head.node() else {
        return Err(record_error(RecordError::InvalidTelescope));
    };
    let Some(ConstantInfo::Induct(family)) = context.txn.env.find(name) else {
        return Err(record_error(RecordError::InvalidTelescope));
    };
    if family.is_rec
        || family.is_unsafe
        || family.num_indices != 0
        || family.ctors.len() != 1
        || arity != family.num_params as usize
        || levels.len() != family.base.level_params.len()
    {
        return Err(record_error(RecordError::InvalidTelescope));
    }
    Ok(name.clone())
}

/// The binder info of each constructor field after its `parameters`.
fn constructor_field_styles(type_: &Expr, parameters: usize) -> Vec<BinderInfo> {
    let mut styles = Vec::new();
    let mut cursor = type_;
    let mut index = 0;
    while let ExprNode::ForallE {
        binder_info, body, ..
    } = cursor.node()
    {
        if index >= parameters {
            styles.push(*binder_info);
        }
        index += 1;
        cursor = body;
    }
    styles
}
