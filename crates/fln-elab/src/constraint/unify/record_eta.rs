//! Bounded structure eta for the native equation worklist (plan §10.2).
//!
//! Only saturated, safe, nonrecursive, nonindexed, Type-valued records take
//! this rung. A neutral's type selects the record; it is not inferred from the
//! constructor on the other side. Type/parameter/universe equations precede
//! field equations, including for empty records. No assignment or environment
//! publication occurs here: every child uses the ordinary solver and every new
//! assignment still crosses the parent's K1 validation barrier.
use super::*;

struct RecordShape {
    name: Name,
    constructor: Name,
    level_params: Vec<Name>,
    family_type: Expr,
    constructor_type: Expr,
    parameters: usize,
    fields: usize,
}

struct RecordApplication {
    shape: RecordShape,
    type_: Expr,
    fields: Vec<Expr>,
}

/// Neutral type synthesis uses heap continuations even for nested projections
/// and applications of projected, function-valued fields.
enum NeutralTypeFrame {
    Application(Expr),
    Projection { structure: Name, index: u64, receiver: Expr },
}

impl Engine<'_> {
    pub(super) fn record_eta(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        let (left_head, left_args) = self.eta_spine(left)?;
        let (right_head, right_args) = self.eta_spine(right)?;
        // Constructor/constructor congruence is already handled by the caller.
        // Expanding both would only recreate the same field equations.
        let left_constructor = matches!(left_head.node(), ExprNode::Const { name, .. }
            if matches!(self.work.env.find(name), Some(ConstantInfo::Ctor(_))));
        let right_constructor = matches!(right_head.node(), ExprNode::Const { name, .. }
            if matches!(self.work.env.find(name), Some(ConstantInfo::Ctor(_))));
        if left_constructor == right_constructor {
            return Ok(false);
        }
        let (head, arguments, neutral, reversed) = if left_constructor {
            (left_head, left_args, right, false)
        } else {
            (right_head, right_args, left, true)
        };
        let Some(record) = self.eta_constructor(&head, arguments, locals)? else {
            return Ok(false);
        };
        let Some(neutral_type) = self.eta_neutral_type(neutral, locals)? else {
            return Ok(false);
        };
        let (type_head, parameters) = self.eta_spine(&neutral_type)?;
        let ExprNode::Const { name, levels } = type_head.node() else {
            // A later equation can reveal this type. Do not guess it now.
            return Ok(false);
        };
        if name != &record.shape.name
            || levels.len() != record.shape.level_params.len()
            || parameters.len() != record.shape.parameters
        {
            return Ok(false);
        }

        // Stage every child before changing the queue. In particular, a stop
        // while allocating projections cannot drop the original obligation.
        let mut children = Vec::new();
        let pair = if reversed {
            (neutral_type, record.type_)
        } else {
            (record.type_, neutral_type)
        };
        self.meter.node()?;
        children.push((pair.0, pair.1, locals.clone()));
        for (index, field) in record.fields.into_iter().enumerate() {
            self.meter.node()?;
            let index = u64::try_from(index).map_err(|_| UnificationError::ExpressionScope)?;
            let projection = Expr::proj(record.shape.name.clone(), index, neutral.clone());
            let pair = if reversed { (projection, field) } else { (field, projection) };
            children.push((pair.0, pair.1, locals.clone()));
        }
        // Full type first, then fields in declaration order. This order matters
        // when a later field's type depends on a parameter or an earlier field.
        for child in children.into_iter().rev() {
            pending.push_front(child);
        }
        Ok(true)
    }

    /// Arguments are returned in application order. Traversal is iterative;
    /// metadata does not change the selected constant or its arity.
    fn eta_spine(&mut self, expr: &Expr) -> Result<(Expr, Vec<Expr>), UnificationError> {
        let mut head = expr.clone();
        let mut arguments = Vec::new();
        loop {
            self.meter.node()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                _ => break,
            }
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    fn eta_shape(&mut self, name: &Name) -> Result<Option<RecordShape>, UnificationError> {
        self.meter.node()?;
        let Some(ConstantInfo::Induct(family)) = self.work.env.find(name) else {
            return Ok(None);
        };
        if family.is_unsafe || family.is_rec || family.is_reflexive
            || family.num_indices != 0 || family.num_nested != 0
            || family.all.len() != 1 || family.all.first() != Some(name)
            || family.ctors.len() != 1 || &family.base.name != name
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Ctor(constructor)) = self.work.env.find(&family.ctors[0]) else {
            return Ok(None);
        };
        if constructor.is_unsafe || constructor.cidx != 0 || &constructor.induct != name
            || constructor.base.name != family.ctors[0]
            || constructor.num_params != family.num_params
            || constructor.base.level_params.len() != family.base.level_params.len()
        {
            return Ok(None);
        }
        // Charge proportional metadata before cloning it.
        for (constructor_level, family_level) in constructor.base.level_params.iter()
            .zip(&family.base.level_params)
        {
            self.meter.node()?;
            if constructor_level != family_level { return Ok(None); }
        }
        Ok(Some(RecordShape {
            name: name.clone(),
            constructor: constructor.base.name.clone(),
            level_params: family.base.level_params.clone(),
            family_type: family.base.type_.clone(),
            constructor_type: constructor.base.type_.clone(),
            parameters: usize::try_from(family.num_params)
                .map_err(|_| UnificationError::ExpressionScope)?,
            fields: usize::try_from(constructor.num_fields)
                .map_err(|_| UnificationError::ExpressionScope)?,
        }))
    }

    fn eta_specialize(
        &mut self,
        type_: &Expr,
        parameters: &[Name],
        levels: &[Level],
    ) -> Result<Expr, UnificationError> {
        self.scan(type_)?;
        crate::universe::parameters::instantiate(
            || self.meter.node(),
            || UnificationError::ExpressionScope,
            type_, parameters, levels,
        )
    }

    fn eta_apply_type(
        &mut self,
        mut type_: Expr,
        arguments: &[Expr],
        locals: &LocalContext,
    ) -> Result<Option<Expr>, UnificationError> {
        for argument in arguments {
            self.meter.node()?;
            type_ = self.instantiate(&type_)?;
            type_ = self.whnf(&type_, locals)?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Ok(None);
            };
            type_ = self.substitute(body, argument)?;
        }
        type_ = self.instantiate(&type_)?;
        Ok(Some(self.whnf(&type_, locals)?))
    }

    fn eta_constructor(
        &mut self,
        head: &Expr,
        mut arguments: Vec<Expr>,
        locals: &LocalContext,
    ) -> Result<Option<RecordApplication>, UnificationError> {
        let head = self.instantiate(head)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.work.env.find(name) else {
            return Ok(None);
        };
        let family = constructor.induct.clone();
        let Some(shape) = self.eta_shape(&family)? else {
            return Ok(None);
        };
        let arity = shape.parameters.checked_add(shape.fields)
            .ok_or(UnificationError::ExpressionScope)?;
        if name != &shape.constructor || levels.len() != shape.level_params.len()
            || arguments.len() != arity
        {
            return Ok(None);
        }
        let family_type = self.eta_specialize(&shape.family_type, &shape.level_params, levels)?;
        let Some(sort) = self.eta_apply_type(family_type, &arguments[..shape.parameters], locals)?
        else {
            return Ok(None);
        };
        if !matches!(sort.node(), ExprNode::Sort { level } if level.is_never_zero()) {
            // Prop and unresolved Prop/Type choices are not this eta rule.
            return Ok(None);
        }
        let constructor_type = self.eta_specialize(
            &shape.constructor_type, &shape.level_params, levels,
        )?;
        let Some(type_) = self.eta_apply_type(constructor_type, &arguments, locals)? else {
            return Ok(None);
        };
        let mut expected = Expr::const_(shape.name.clone(), levels.clone());
        for argument in &arguments[..shape.parameters] {
            self.meter.node()?;
            expected = Expr::app(expected, argument.clone());
        }
        expected = self.instantiate(&expected)?;
        if !same_terms(&type_, &expected, &mut self.meter)? {
            return Ok(None);
        }
        let fields = arguments.split_off(shape.parameters);
        Ok(Some(RecordApplication { shape, type_, fields }))
    }

    /// Synthesize only a neutral spine's type. This is a candidate-selection
    /// aid, not a type checker or an alternative to K1 assignment validation.
    /// Unknown heads, malformed applications and blocked types defer.
    fn eta_neutral_type(
        &mut self,
        expr: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<Expr>, UnificationError> {
        let mut head = expr.clone();
        let mut frames = Vec::new();
        loop {
            self.meter.node()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    frames.push(NeutralTypeFrame::Application(a.clone()));
                    head = f.clone();
                }
                ExprNode::Proj { struct_name, idx, expr } => {
                    frames.push(NeutralTypeFrame::Projection {
                        structure: struct_name.clone(), index: *idx, receiver: expr.clone(),
                    });
                    head = expr.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                _ => break,
            }
        }
        let type_ = match head.node() {
            ExprNode::FVar { id } => locals.find(id).map(|local| local.type_.clone()),
            ExprNode::MVar { id } => self.work.mvars.get_decl(id).map(|local| local.type_.clone()),
            ExprNode::Const { name, levels } => {
                let Some(info) = self.work.env.find(name) else {
                    return Ok(None);
                };
                let safe = match info {
                    ConstantInfo::Axiom(v) => !v.is_unsafe,
                    ConstantInfo::Defn(v) => v.safety == DefinitionSafety::Safe,
                    ConstantInfo::Opaque(v) => !v.is_unsafe,
                    ConstantInfo::Induct(v) => !v.is_unsafe,
                    ConstantInfo::Ctor(v) => !v.is_unsafe,
                    ConstantInfo::Rec(v) => !v.is_unsafe,
                    ConstantInfo::Thm(_) | ConstantInfo::Quot(_) => true,
                };
                let base = info.constant_val();
                if !safe || base.level_params.len() != levels.len() {
                    return Ok(None);
                }
                for _ in &base.level_params {
                    self.meter.node()?;
                }
                let parameters = base.level_params.clone();
                let type_ = base.type_.clone();
                Some(self.eta_specialize(&type_, &parameters, levels)?)
            }
            _ => None,
        };
        let Some(mut type_) = type_ else { return Ok(None); };
        while let Some(frame) = frames.pop() {
            self.meter.node()?;
            let next = match frame {
                NeutralTypeFrame::Application(argument) => {
                    self.eta_apply_type(type_, std::slice::from_ref(&argument), locals)?
                }
                NeutralTypeFrame::Projection { structure, index, receiver } => {
                    self.eta_projection_type(type_, &structure, index, &receiver, locals)?
                }
            };
            let Some(next) = next else { return Ok(None); };
            type_ = next;
        }
        self.eta_apply_type(type_, &[], locals)
    }

    /// A dependent field's domain refers to earlier projections of this exact
    /// receiver. Substituting fresh, unrelated field locals here would allow
    /// parameter inference to escape the record that was actually projected.
    fn eta_projection_type(
        &mut self,
        receiver_type: Expr,
        structure: &Name,
        index: u64,
        receiver: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<Expr>, UnificationError> {
        let Some(receiver_type) = self.eta_apply_type(receiver_type, &[], locals)? else {
            return Ok(None);
        };
        let (head, parameters) = self.eta_spine(&receiver_type)?;
        let ExprNode::Const { name, levels } = head.node() else { return Ok(None); };
        if name != structure { return Ok(None); }
        let Some(shape) = self.eta_shape(structure)? else { return Ok(None); };
        if parameters.len() != shape.parameters || levels.len() != shape.level_params.len()
            || index >= u64::try_from(shape.fields).map_err(|_| UnificationError::ExpressionScope)?
        {
            return Ok(None);
        }
        let family_type = self.eta_specialize(&shape.family_type, &shape.level_params, levels)?;
        let Some(sort) = self.eta_apply_type(family_type, &parameters, locals)? else {
            return Ok(None);
        };
        if !matches!(sort.node(), ExprNode::Sort { level } if level.is_never_zero()) {
            return Ok(None);
        }
        let constructor_type = self.eta_specialize(
            &shape.constructor_type, &shape.level_params, levels,
        )?;
        let Some(mut type_) = self.eta_apply_type(constructor_type, &parameters, locals)? else {
            return Ok(None);
        };
        let mut selected = None;
        for prior in 0..shape.fields {
            self.meter.node()?;
            type_ = self.instantiate(&type_)?;
            type_ = self.whnf(&type_, locals)?;
            let ExprNode::ForallE { binder_type, body, .. } = type_.node() else {
                return Ok(None);
            };
            let prior = u64::try_from(prior).map_err(|_| UnificationError::ExpressionScope)?;
            if prior == index { selected = Some(binder_type.clone()); }
            self.meter.node()?;
            let field = Expr::proj(structure.clone(), prior, receiver.clone());
            type_ = self.substitute(body, &field)?;
        }
        let Some(result) = self.eta_apply_type(type_, &[], locals)? else {
            return Ok(None);
        };
        // Metadata is not a license to infer a field of a different family.
        if !same_terms(&result, &receiver_type, &mut self.meter)? {
            return Ok(None);
        }
        match selected {
            Some(type_) => self.eta_apply_type(type_, &[], locals),
            None => Ok(None),
        }
    }
}
