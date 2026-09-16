//! Elaborate disjoint parent subobjects and aliases in the declaration's scope.
//! Aliases are eliminated before constructor/default generation; only physical
//! parent fields enter the record telescope. No declaration is admitted here.
use super::*;
use crate::instances::InstanceRegistry;
use crate::records::RecordError;
use crate::records::inheritance::{RecordParent, RecordParents};
use fln_core::name::LeafView;
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;

pub(super) struct Inheritance {
    pub fields: Vec<LocalDecl>,
    pub aliases: Vec<LocalDecl>,
    pub parents: Vec<RecordParent>,
    pub instances: Vec<Name>,
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
            instances: Vec::new(),
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
        let classes = InstanceRegistry::read(&self.txn.env)
            .map_err(|e| failure(SourceInferenceError::InstanceRegistry(e)))?;
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
            let mut head = &type_;
            let mut arity = 0usize;
            while let ExprNode::App { f, .. } = head.node() {
                self.tick()?;
                arity += 1;
                head = f;
            }
            let ExprNode::Const { name, levels } = head.node() else {
                return Err(record_error(RecordError::InvalidTelescope));
            };
            let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name) else {
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
            let name = name.clone();
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
            let completed = self.finish(Typed {
                value: type_,
                type_: sort,
            })?;
            let level = self.sort_level(&completed)?;
            result.level = Level::max(result.level, level)
                .map_err(|_| record_error(RecordError::ResourceLimit))?;
            let style = if is_class && classes.is_class(&name) {
                BinderInfo::InstImplicit
            } else {
                BinderInfo::Default
            };
            let id = FVarId(self.fresh_name()?);
            let local = self
                .txn
                .lctx
                .add_param(id.clone(), label.clone(), completed.value.clone(), style)
                .clone();
            if style == BinderInfo::InstImplicit {
                result.instances.push(record.append_core(&label));
            }
            result.parents.push(RecordParent {
                record: record.clone(),
                field: result.fields.len() as u32,
                parent: name.clone(),
            });
            result.fields.push(local);
            let receiver = Typed {
                value: Expr::fvar(id),
                type_: completed.value,
            };
            for field in registry
                .fields(&self.txn.env, &name, budget)
                .map_err(record_error)?
            {
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
        }
        Ok(result)
    }
}
