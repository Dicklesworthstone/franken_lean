//! Named record construction. Field names select constructor arguments, never
//! independent declarations or trusted projections. Elaboration follows the
//! constructor telescope so later field types see the actual earlier values.
use super::*;
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
}
pub(super) struct RecordBuild<'a> {
    fields: HashMap<Name, &'a Syntax>,
    constructor: Typed,
    remaining: u32,
    expected: Expr,
}
pub(super) enum RecordStep<'a> {
    Field {
        syntax: &'a Syntax,
        domain: Expr,
        codomain: Expr,
    },
    Complete(Typed),
}

impl Context {
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
        expect_empty_null(&parts[1], "unsupported record update sources")?;
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
        Ok(RecordParts { fields, annotation })
    }

    pub(super) fn start_record<'a>(
        &mut self,
        parts: RecordParts<'a>,
        expected: Option<Expr>,
    ) -> Result<RecordBuild<'a>, NatDefinitionElabError> {
        self.flush(false)?;
        let expected = expected.ok_or_else(|| error(RecordTermError::ExpectedRecordType))?;
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
        Ok(RecordBuild {
            fields: parts.fields.into_iter().collect(),
            constructor,
            remaining: ctor.num_fields,
            expected,
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
            return Ok(RecordStep::Complete(
                self.finish_term(state.constructor.clone(), Some(&state.expected))?,
            ));
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
        let syntax = state
            .fields
            .remove(binder_name)
            .ok_or_else(|| error(RecordTermError::MissingField(binder_name.clone())))?;
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
