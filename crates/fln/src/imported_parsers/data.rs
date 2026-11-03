//! Closed parser-description data, reduced from its actual admitted definitions.
//!
//! This small evaluator performs only delta, beta, zeta, metadata erasure and
//! checked record projection. It has no named helper shortcuts, recursor rules,
//! arithmetic primitives, opaque execution or Reference/VM fallback. Closures
//! retain their lexical bindings, so substitution cannot duplicate a large term
//! before the caller's work budget observes it.

use fln_core::expr::{Expr, ExprNode, Literal};
use fln_core::level::{Level, LevelView};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
use fln_olean::source_extensions::parsers::{
    PARSER_BOOL_CONSTRUCTOR_FIELDS, PARSER_NAME_CONSTRUCTOR_FIELDS, PARSER_NAT_CONSTRUCTOR_FIELDS,
    PARSER_TYPE_ALIASES,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

type ConstructorFields = &'static [(&'static str, &'static [&'static str])];
type Universes = Arc<[(Name, Level)]>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct DataLimits {
    pub max_steps: usize,
    pub max_depth: usize,
    pub max_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum DataError {
    Unsupported(&'static str),
    Resource(&'static str),
    Missing(Name),
    NotPermitted(Name),
}

/// A closed expression, or a subexpression under its immutable lexical scope.
#[derive(Clone)]
pub(super) struct Value {
    expression: Expr,
    locals: Option<Arc<Binding>>,
    universes: Universes,
    depth: usize,
}

struct Binding {
    value: Value,
    previous: Option<Arc<Binding>>,
    depth: usize,
}

impl Drop for Binding {
    fn drop(&mut self) {
        // A high caller-selected depth must not turn cleanup into recursive
        // host-stack work. Each detached scope owns only older immutable
        // scopes; shared ones are left for their final owner to drain.
        let mut pending = Vec::new();
        pending.extend(self.previous.take());
        pending.extend(self.value.locals.take());
        while let Some(binding) = pending.pop() {
            if let Ok(mut binding) = Arc::try_unwrap(binding) {
                pending.extend(binding.previous.take());
                pending.extend(binding.value.locals.take());
            }
        }
    }
}

impl Value {
    pub(super) fn closed(expression: Expr) -> Self {
        Self {
            expression,
            locals: None,
            universes: Arc::from([]),
            depth: 0,
        }
    }
}

enum Head {
    Constant { name: Name, levels: Vec<Level> },
    Literal(Expr),
    Sort(Level),
    Forall { domain: Value, body: Value },
    Lambda,
}

struct Normal {
    head: Head,
    /// Ordinary left-to-right application order.
    arguments: Vec<Value>,
}

struct Projection {
    structure: Name,
    index: u64,
    arguments: Vec<Value>,
}

pub(super) struct Reader<'a> {
    environment: &'a Environment,
    allowed: &'a BTreeSet<Name>,
    remaining: DataLimits,
    used: BTreeSet<Name>,
    validated: BTreeMap<Name, ConstructorFields>,
}

fn name(spelling: &str) -> Name {
    Name::from_components(spelling.split('.'))
}

fn unsupported(reason: &'static str) -> DataError {
    DataError::Unsupported(reason)
}

impl<'a> Reader<'a> {
    pub(super) fn new(
        environment: &'a Environment,
        allowed: &'a BTreeSet<Name>,
        limits: DataLimits,
    ) -> Self {
        Self {
            environment,
            allowed,
            remaining: limits,
            used: BTreeSet::new(),
            validated: BTreeMap::new(),
        }
    }

    pub(super) fn remaining_limits(&self) -> DataLimits {
        self.remaining
    }

    #[cfg(test)]
    pub(super) fn used(&self) -> &BTreeSet<Name> {
        &self.used
    }

    pub(super) fn into_used(self) -> BTreeSet<Name> {
        self.used
    }

    fn tick(&mut self) -> Result<(), DataError> {
        self.remaining.max_steps = self
            .remaining
            .max_steps
            .checked_sub(1)
            .ok_or(DataError::Resource("parser-description data steps"))?;
        Ok(())
    }

    fn depth(&self, depth: usize) -> Result<(), DataError> {
        if depth > self.remaining.max_depth {
            return Err(DataError::Resource("parser-description data depth"));
        }
        Ok(())
    }

    fn bytes(&mut self, bytes: usize) -> Result<(), DataError> {
        self.remaining.max_bytes = self
            .remaining
            .max_bytes
            .checked_sub(bytes)
            .ok_or(DataError::Resource("parser-description data bytes"))?;
        Ok(())
    }

    fn declaration(&mut self, symbol: &Name) -> Result<&'a ConstantInfo, DataError> {
        self.tick()?;
        if !self.allowed.contains(symbol) {
            return Err(DataError::NotPermitted(symbol.clone()));
        }
        let declaration = self
            .environment
            .find(symbol)
            .ok_or_else(|| DataError::Missing(symbol.clone()))?;
        self.used.insert(symbol.clone());
        Ok(declaration)
    }

    fn child(&mut self, parent: &Value, expression: Expr) -> Result<Value, DataError> {
        self.tick()?;
        let depth = parent
            .depth
            .checked_add(1)
            .ok_or(DataError::Resource("parser-description data depth"))?;
        self.depth(depth)?;
        Ok(Value {
            expression,
            locals: parent.locals.clone(),
            universes: parent.universes.clone(),
            depth,
        })
    }

    fn bind(&mut self, parent: &Value, body: Expr, argument: Value) -> Result<Value, DataError> {
        let mut result = self.child(parent, body)?;
        let depth = parent.locals.as_ref().map_or(0, |local| local.depth);
        let depth = depth
            .checked_add(1)
            .ok_or(DataError::Resource("parser-description local depth"))?;
        self.depth(depth)?;
        result.locals = Some(Arc::new(Binding {
            value: argument,
            previous: parent.locals.clone(),
            depth,
        }));
        Ok(result)
    }

    fn local(&mut self, value: &Value, index: u32) -> Result<Value, DataError> {
        let mut cursor = value.locals.as_ref();
        for _ in 0..index {
            self.tick()?;
            cursor = cursor.and_then(|local| local.previous.as_ref());
            if cursor.is_none() {
                return Err(unsupported("open parser-description data"));
            }
        }
        self.tick()?;
        cursor
            .map(|local| local.value.clone())
            .ok_or_else(|| unsupported("open parser-description data"))
    }

    fn level(&mut self, level: &Level, universes: &Universes) -> Result<Level, DataError> {
        enum Work<'l> {
            Visit(&'l Level, usize),
            Succ,
            Max,
            IMax,
        }
        let mut work = vec![Work::Visit(level, 0)];
        let mut values = Vec::<Level>::new();
        while let Some(item) = work.pop() {
            self.tick()?;
            match item {
                Work::Visit(level, depth) => {
                    self.depth(depth)?;
                    let next_depth = depth
                        .checked_add(1)
                        .ok_or(DataError::Resource("parser-description universe depth"))?;
                    match level.view() {
                        LevelView::Zero => values.push(Level::zero()),
                        LevelView::Param(parameter) => {
                            let mut replacement = None;
                            for (name, level) in universes.iter() {
                                self.tick()?;
                                if name == parameter {
                                    replacement = Some(level.clone());
                                    break;
                                }
                            }
                            values.push(
                                replacement.ok_or_else(|| {
                                    unsupported("open parser-description universe")
                                })?,
                            );
                        }
                        LevelView::MVar(_) => {
                            return Err(unsupported("parser-description universe metavariable"));
                        }
                        LevelView::Succ(inner) => {
                            work.push(Work::Succ);
                            work.push(Work::Visit(inner, next_depth));
                        }
                        LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                            work.push(if matches!(level.view(), LevelView::Max(_, _)) {
                                Work::Max
                            } else {
                                Work::IMax
                            });
                            work.push(Work::Visit(right, next_depth));
                            work.push(Work::Visit(left, next_depth));
                        }
                    }
                }
                Work::Succ => {
                    let value = values
                        .pop()
                        .ok_or_else(|| unsupported("parser-description universe stack"))?;
                    values.push(
                        value
                            .succ()
                            .map_err(|_| unsupported("parser-description universe depth"))?,
                    );
                }
                Work::Max | Work::IMax => {
                    let right = values
                        .pop()
                        .ok_or_else(|| unsupported("parser-description universe stack"))?;
                    let left = values
                        .pop()
                        .ok_or_else(|| unsupported("parser-description universe stack"))?;
                    let result = if matches!(item, Work::Max) {
                        Level::max(left, right)
                    } else {
                        Level::imax(left, right)
                    };
                    values.push(
                        result.map_err(|_| unsupported("parser-description universe depth"))?,
                    );
                }
            }
        }
        if values.len() != 1 {
            return Err(unsupported("parser-description universe stack"));
        }
        values
            .pop()
            .ok_or_else(|| unsupported("parser-description universe stack"))
    }

    fn levels(&mut self, levels: &[Level], universes: &Universes) -> Result<Vec<Level>, DataError> {
        let mut result = Vec::new();
        for level in levels {
            self.tick()?;
            result.push(self.level(level, universes)?);
        }
        Ok(result)
    }

    /// Reduce a head using only the admitted expression syntax. Argument thunks
    /// retain the caller's universe and local environments across each delta.
    fn whnf(&mut self, mut value: Value) -> Result<Normal, DataError> {
        let mut arguments = Vec::new();
        let mut projections = Vec::new();
        loop {
            self.tick()?;
            self.depth(value.depth)?;
            if value.expression.has_fvar() || value.expression.has_expr_mvar() {
                return Err(unsupported("open parser-description data"));
            }
            let head = match value.expression.node() {
                ExprNode::BVar { idx } => {
                    value = self.local(&value, *idx)?;
                    continue;
                }
                ExprNode::MData { expr, .. } => {
                    value = self.child(&value, expr.clone())?;
                    continue;
                }
                ExprNode::App { f, a } => {
                    self.depth(arguments.len().saturating_add(1))?;
                    arguments.push(self.child(&value, a.clone())?);
                    value = self.child(&value, f.clone())?;
                    continue;
                }
                ExprNode::LetE {
                    value: bound, body, ..
                } => {
                    let argument = self.child(&value, bound.clone())?;
                    value = self.bind(&value, body.clone(), argument)?;
                    continue;
                }
                ExprNode::Lam { body, .. } => {
                    if let Some(argument) = arguments.pop() {
                        value = self.bind(&value, body.clone(), argument)?;
                        continue;
                    }
                    Head::Lambda
                }
                ExprNode::Const { name, levels } => {
                    let declaration = self.declaration(name)?;
                    let levels = self.levels(levels, &value.universes)?;
                    if declaration.constant_val().level_params.len() != levels.len() {
                        return Err(unsupported("parser-description constant universe arity"));
                    }
                    match declaration {
                        ConstantInfo::Defn(definition) => {
                            if definition.safety != DefinitionSafety::Safe {
                                return Err(unsupported("non-safe parser-description definition"));
                            }
                            let mut universes = Vec::new();
                            for (parameter, level) in
                                definition.base.level_params.iter().zip(levels)
                            {
                                self.tick()?;
                                universes.push((parameter.clone(), level));
                            }
                            let mut next = self.child(&value, definition.value.clone())?;
                            next.locals = None;
                            next.universes = universes.into();
                            value = next;
                            continue;
                        }
                        ConstantInfo::Ctor(_)
                        | ConstantInfo::Induct(_)
                        | ConstantInfo::Axiom(_) => Head::Constant {
                            name: name.clone(),
                            levels,
                        },
                        ConstantInfo::Opaque(_)
                        | ConstantInfo::Thm(_)
                        | ConstantInfo::Rec(_)
                        | ConstantInfo::Quot(_) => {
                            return Err(unsupported("executable parser-description data"));
                        }
                    }
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    self.depth(projections.len().saturating_add(1))?;
                    projections.push(Projection {
                        structure: struct_name.clone(),
                        index: *idx,
                        arguments: std::mem::take(&mut arguments),
                    });
                    value = self.child(&value, expr.clone())?;
                    continue;
                }
                ExprNode::Lit { .. } => Head::Literal(value.expression.clone()),
                ExprNode::Sort { level } => Head::Sort(self.level(level, &value.universes)?),
                ExprNode::ForallE {
                    binder_type, body, ..
                } => Head::Forall {
                    domain: self.child(&value, binder_type.clone())?,
                    body: self.child(&value, body.clone())?,
                },
                ExprNode::FVar { .. } | ExprNode::MVar { .. } => {
                    return Err(unsupported("open parser-description data"));
                }
            };
            arguments.reverse();
            let normal = Normal { head, arguments };
            let Some(projection) = projections.pop() else {
                return Ok(normal);
            };
            value = self.project(&projection.structure, projection.index, normal)?;
            arguments = projection.arguments;
        }
    }

    fn constructor_normal(&mut self, normal: Normal) -> Result<(Name, Vec<Value>), DataError> {
        let Head::Constant { name, levels } = normal.head else {
            return Err(unsupported("parser-description constructor value"));
        };
        let ConstantInfo::Ctor(constructor) = self.declaration(&name)? else {
            return Err(unsupported(
                "parser-description head is not an admitted constructor",
            ));
        };
        let ConstantInfo::Induct(family) = self.declaration(&constructor.induct)? else {
            return Err(unsupported(
                "parser-description constructor has no admitted family",
            ));
        };
        let arity = u64::from(constructor.num_params) + u64::from(constructor.num_fields);
        if constructor.is_unsafe
            || family.is_unsafe
            || constructor.num_params != family.num_params
            || constructor.base.level_params != family.base.level_params
            || levels.len() != constructor.base.level_params.len()
            || usize::try_from(constructor.cidx)
                .ok()
                .and_then(|index| family.ctors.get(index))
                != Some(&name)
            || u64::try_from(normal.arguments.len()).ok() != Some(arity)
        {
            return Err(unsupported("parser-description constructor interface"));
        }
        Ok((name, normal.arguments))
    }

    fn project(
        &mut self,
        structure: &Name,
        index: u64,
        normal: Normal,
    ) -> Result<Value, DataError> {
        let ConstantInfo::Induct(family) = self.declaration(structure)? else {
            return Err(unsupported("parser-description projection family"));
        };
        if family.is_unsafe || family.num_indices != 0 || family.ctors.len() != 1 {
            return Err(unsupported(
                "parser-description projection is not a safe record",
            ));
        }
        let (constructor_name, arguments) = self.constructor_normal(normal)?;
        let ConstantInfo::Ctor(constructor) = self.declaration(&constructor_name)? else {
            return Err(unsupported("parser-description projection constructor"));
        };
        if constructor_name != family.ctors[0]
            || &constructor.induct != structure
            || index >= u64::from(constructor.num_fields)
        {
            return Err(unsupported("parser-description projection receiver"));
        }
        let position = usize::try_from(u64::from(constructor.num_params) + index)
            .map_err(|_| unsupported("parser-description projection field"))?;
        arguments
            .get(position)
            .cloned()
            .ok_or_else(|| unsupported("parser-description projection field"))
    }

    pub(super) fn constructor(&mut self, value: Value) -> Result<(Name, Vec<Value>), DataError> {
        let normal = self.whnf(value)?;
        self.constructor_normal(normal)
    }

    fn type_name(&mut self, value: Value) -> Result<Name, DataError> {
        let normal = self.whnf(value)?;
        match normal.head {
            Head::Constant { name, levels } if normal.arguments.is_empty() && levels.is_empty() => {
                if matches!(self.declaration(&name)?, ConstantInfo::Induct(info) if !info.is_unsafe)
                    || matches!(self.declaration(&name)?, ConstantInfo::Axiom(info) if !info.is_unsafe)
                {
                    Ok(name)
                } else {
                    Err(unsupported("parser-description field type"))
                }
            }
            _ => Err(unsupported("parser-description field type")),
        }
    }

    pub(super) fn expected_type(&mut self, spelling: &str) -> Result<Name, DataError> {
        let declared = name(spelling);
        let actual = self.type_name(Value::closed(Expr::const_(declared.clone(), vec![])))?;
        let expected = PARSER_TYPE_ALIASES
            .iter()
            .find_map(|(alias, target)| (*alias == spelling).then(|| name(target)))
            .unwrap_or(declared);
        if actual != expected {
            return Err(unsupported("parser-description data type alias interface"));
        }
        Ok(expected)
    }

    /// Verify the entire source-derived datatype interface, not only a familiar
    /// constructor name. Aliases in field types reduce through their real bodies.
    pub(super) fn validate_family(
        &mut self,
        family_name: &Name,
        fields: ConstructorFields,
    ) -> Result<(), DataError> {
        self.tick()?;
        if let Some(previous) = self.validated.get(family_name) {
            return if *previous == fields {
                Ok(())
            } else {
                Err(unsupported(
                    "conflicting parser-description datatype contracts",
                ))
            };
        }
        let ConstantInfo::Induct(family) = self.declaration(family_name)? else {
            return Err(unsupported(
                "parser-description data family is not inductive",
            ));
        };
        if family.is_unsafe
            || family.num_params != 0
            || family.num_indices != 0
            || family.num_nested != 0
            || family.all != [family_name.clone()]
            || !family.base.level_params.is_empty()
            || family.ctors.len() != fields.len()
        {
            return Err(unsupported("parser-description data family interface"));
        }
        let universe = self.whnf(Value::closed(family.base.type_.clone()))?;
        if !universe.arguments.is_empty()
            || !matches!(universe.head, Head::Sort(level) if level == Level::one())
        {
            return Err(unsupported("parser-description data family universe"));
        }
        for (index, (spelling, expected_fields)) in fields.iter().enumerate() {
            self.tick()?;
            let symbol = name(spelling);
            if family.ctors[index] != symbol {
                return Err(unsupported("parser-description data constructor order"));
            }
            let ConstantInfo::Ctor(constructor) = self.declaration(&symbol)? else {
                return Err(unsupported(
                    "parser-description data constructor declaration",
                ));
            };
            if constructor.is_unsafe
                || &constructor.induct != family_name
                || usize::try_from(constructor.cidx).ok() != Some(index)
                || constructor.num_params != 0
                || usize::try_from(constructor.num_fields).ok() != Some(expected_fields.len())
                || !constructor.base.level_params.is_empty()
            {
                return Err(unsupported("parser-description data constructor interface"));
            }
            let mut type_ = Value::closed(constructor.base.type_.clone());
            for expected in *expected_fields {
                let normal = self.whnf(type_)?;
                if !normal.arguments.is_empty() {
                    return Err(unsupported("parser-description constructor telescope"));
                }
                let Head::Forall { domain, body } = normal.head else {
                    return Err(unsupported("parser-description constructor telescope"));
                };
                let actual = self.type_name(domain)?;
                let expected = self.expected_type(expected)?;
                if actual != expected {
                    return Err(unsupported("parser-description constructor field type"));
                }
                type_ = body;
            }
            if self.type_name(type_)? != *family_name {
                return Err(unsupported("parser-description constructor result type"));
            }
        }
        self.validated.insert(family_name.clone(), fields);
        Ok(())
    }

    pub(super) fn string(&mut self, value: Value) -> Result<String, DataError> {
        let normal = self.whnf(value)?;
        if !normal.arguments.is_empty() {
            return Err(unsupported("applied parser-description string"));
        }
        let Head::Literal(expression) = normal.head else {
            return Err(unsupported("computed parser-description string"));
        };
        let ExprNode::Lit {
            literal: Literal::Str(text),
        } = expression.node()
        else {
            return Err(unsupported("parser-description string value"));
        };
        self.bytes(text.len())?;
        Ok(text.clone())
    }

    fn nat_u64(&mut self, mut value: Value) -> Result<u64, DataError> {
        self.validate_family(&name("Nat"), PARSER_NAT_CONSTRUCTOR_FIELDS)?;
        let mut successors = 0_u64;
        loop {
            let normal = self.whnf(value)?;
            if normal.arguments.is_empty()
                && let Head::Literal(expression) = &normal.head
                && let ExprNode::Lit {
                    literal: Literal::Nat(number),
                } = expression.node()
            {
                return number
                    .to_u64()
                    .and_then(|number| number.checked_add(successors))
                    .ok_or(DataError::Resource(
                        "parser-description natural number exceeds u64",
                    ));
            }
            let (constructor, mut arguments) = self.constructor_normal(normal)?;
            if constructor == name("Nat.zero") && arguments.is_empty() {
                return Ok(successors);
            }
            if constructor != name("Nat.succ") || arguments.len() != 1 {
                return Err(unsupported("parser-description natural number constructor"));
            }
            successors = successors.checked_add(1).ok_or(DataError::Resource(
                "parser-description natural number exceeds u64",
            ))?;
            value = arguments
                .pop()
                .ok_or_else(|| unsupported("parser-description Nat.succ field"))?;
        }
    }

    pub(super) fn nat_u32(&mut self, value: Value) -> Result<u32, DataError> {
        u32::try_from(self.nat_u64(value)?)
            .map_err(|_| DataError::Resource("parser-description natural number exceeds u32"))
    }

    pub(super) fn boolean(&mut self, value: Value) -> Result<bool, DataError> {
        self.validate_family(&name("Bool"), PARSER_BOOL_CONSTRUCTOR_FIELDS)?;
        let (constructor, arguments) = self.constructor(value)?;
        if !arguments.is_empty() {
            return Err(unsupported("applied parser-description Boolean"));
        }
        if constructor == name(PARSER_BOOL_CONSTRUCTOR_FIELDS[0].0) {
            Ok(false)
        } else if constructor == name(PARSER_BOOL_CONSTRUCTOR_FIELDS[1].0) {
            Ok(true)
        } else {
            Err(unsupported("parser-description Boolean constructor"))
        }
    }

    pub(super) fn name(&mut self, mut value: Value) -> Result<Name, DataError> {
        self.validate_family(&name("Lean.Name"), PARSER_NAME_CONSTRUCTOR_FIELDS)?;
        enum Component {
            Text(String),
            Number(u64),
        }
        let mut components = Vec::new();
        loop {
            let (constructor, mut arguments) = self.constructor(value)?;
            if constructor == name(PARSER_NAME_CONSTRUCTOR_FIELDS[0].0) && arguments.is_empty() {
                break;
            }
            if arguments.len() != 2 {
                return Err(unsupported("parser-description name constructor"));
            }
            let part = arguments
                .pop()
                .ok_or_else(|| unsupported("parser-description name field"))?;
            let component = if constructor == name(PARSER_NAME_CONSTRUCTOR_FIELDS[1].0) {
                Component::Text(self.string(part)?)
            } else if constructor == name(PARSER_NAME_CONSTRUCTOR_FIELDS[2].0) {
                Component::Number(self.nat_u64(part)?)
            } else {
                return Err(unsupported("parser-description name constructor"));
            };
            self.depth(components.len().saturating_add(1))?;
            components.push(component);
            value = arguments
                .pop()
                .ok_or_else(|| unsupported("parser-description name prefix"))?;
        }
        let mut result = Name::anonymous();
        for component in components.into_iter().rev() {
            self.tick()?;
            result = match component {
                Component::Text(text) => Name::str(result, &text),
                Component::Number(number) => Name::num(result, number),
            };
        }
        Ok(result)
    }
}

#[cfg(test)]
pub(crate) mod tests;
