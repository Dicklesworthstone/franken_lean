//! Native elimination of admitted ground mutual families. Family-local tags
//! remain separate layouts; a branch projects only its selected constructor.
use super::*;
use fln_core::{expr::FVarId, level::Level};
use fln_env::constants::RecursorVal;
mod fold;

pub(super) struct Fold {
    pub group: u32,
    pub selected: usize,
    pub members: Vec<Member>,
    pub arguments: Vec<Expr>,
}

pub(super) struct Member {
    pub name: Name,
    pub self_type: Expr,
    pub domains: Vec<Expr>,
    pub parameters: Vec<ValueType>,
    pub case: variants::Case,
}

pub(super) struct Group {
    shapes: Vec<records::Shape>,
    selected: usize,
    minor_offset: usize,
    arity: usize,
}

impl Preparation<'_> {
    fn mutual_group(
        &mut self,
        rec: &RecursorVal,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Group>, IngressError> {
        if rec.is_unsafe
            || rec.num_indices != 0
            || rec.all.len() < 2
            || rec.num_motives as usize != rec.all.len()
            || levels.len() != rec.base.level_params.len()
            || args.len() < rec.num_params as usize
        {
            return Ok(None);
        }
        let Some(rule) = rec.rules.first() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(&rule.ctor) else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(&ctor.induct) else {
            return Ok(None);
        };
        if family.all != rec.all || family.num_params != rec.num_params {
            return Ok(None);
        }
        let Some(selected) = rec.all.iter().position(|name| name == &ctor.induct) else {
            return Ok(None);
        };
        let mut family_levels = Vec::new();
        for parameter in &family.base.level_params {
            self.tick()?;
            let Some(index) = rec
                .base
                .level_params
                .iter()
                .position(|name| name == parameter)
            else {
                return Ok(None);
            };
            reserve(&mut family_levels, self.limits.max_context_depth)?;
            family_levels.push(levels[index].clone());
        }
        let mut source = Expr::const_(family.base.name.clone(), family_levels);
        for parameter in &args[..rec.num_params as usize] {
            self.tick()?;
            source = Expr::app(source, parameter.clone());
        }
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Ok(None);
        }
        let Some(shapes) = self.record_group(&source)? else {
            return Ok(None);
        };
        let mut total = 0usize;
        let mut minor_offset = 0;
        for (index, shape) in shapes.iter().enumerate() {
            self.tick()?;
            if index == selected {
                minor_offset = total;
            }
            total = total
                .checked_add(shape.constructors.len())
                .ok_or_else(|| unsupported("mutual constructor count"))?;
        }
        let shape = &shapes[selected];
        if rec.num_minors as usize != total
            || rec.rules.len() != shape.constructors.len()
            || rec
                .rules
                .iter()
                .zip(&shape.constructors)
                .any(|(rule, ctor)| {
                    rule.ctor != ctor.original || rule.nfields as usize != ctor.fields.len()
                })
        {
            return Ok(None);
        }
        let arity = (rec.num_params as usize)
            .checked_add(shapes.len())
            .and_then(|n| n.checked_add(total))
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| unsupported("mutual recursor arity"))?;
        Ok(Some(Group {
            shapes,
            selected,
            minor_offset,
            arity,
        }))
    }

    /// An ordinary match does not consume any induction hypothesis. Open the
    /// actual selected minors with private markers to establish that fact,
    /// rather than evaluating sibling recursors or inventing dummy values.
    pub(super) fn mutual_case(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<variants::Case>, IngressError> {
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        let Some(group) = self.mutual_group(rec, levels, args)? else {
            return Ok(None);
        };
        if args.len() != group.arity {
            return Ok(None);
        }
        let shape = &group.shapes[group.selected];
        let ExprNode::Lam {
            binder_type,
            body: motive,
            ..
        } = args[rec.num_params as usize + group.selected].node()
        else {
            return Ok(None);
        };
        if self.normalize_type(binder_type)? != shape.source || motive.has_loose_bvars() {
            return Ok(None);
        }
        let result = self
            .value_type(motive)?
            .ok_or_else(|| unsupported("dependent mutual match result"))?;
        let id = self.next_variant;
        self.next_variant = id
            .checked_add(1)
            .ok_or_else(|| unsupported("mutual case identity"))?;
        let case_name = Name::num(super::name("_fln_runtime_mutual_case"), id);
        if self.environment.contains(&case_name) {
            return Err(unsupported("runtime mutual case name collision"));
        }
        let major = Expr::bvar(0).map_err(|_| unsupported("mutual major scope"))?;
        let mut branches = Vec::new();
        let mut constructors = Vec::new();
        for (index, ctor) in shape.constructors.iter().enumerate() {
            self.tick()?;
            let minor = rec.num_params as usize + group.shapes.len() + group.minor_offset + index;
            let mut body = self.lift(&args[minor], 1)?;
            let mut hypotheses = Vec::new();
            for (field, type_) in ctor.fields.iter().enumerate() {
                self.tick()?;
                body = self.minor_apply(
                    body,
                    Expr::proj(shape.projection(ctor), field as u64, major.clone()),
                )?;
                if group.shapes.iter().any(|shape| &shape.source == type_) {
                    reserve(&mut hypotheses, self.limits.max_context_depth)?;
                    hypotheses.push(FVarId(Name::num(case_name.clone(), field as u64)));
                }
            }
            for marker in hypotheses {
                self.tick()?;
                body = self.minor_apply(body, Expr::fvar(marker))?;
            }
            // A retained marker means this is a fold, not a plain case split.
            // It must use the recursive lowering, never a made-up IH value.
            if body.has_fvar() {
                return Ok(None);
            }
            let body = self.typed_callable_result(body, motive.clone(), result)?;
            reserve(&mut branches, self.limits.max_lambda_bindings)?;
            branches.push(Expr::lam(
                Name::num(case_name.clone(), index as u64),
                shape.source.clone(),
                body,
                BinderInfo::Default,
            ));
            reserve(&mut constructors, self.limits.fir.max_constructors)?;
            constructors.push(ctor.name.clone());
        }
        reserve(&mut self.variant_cases, self.limits.fir.max_functions)?;
        self.variant_cases.push(ConstructorCaseBinding {
            name: case_name.clone(),
            constructors,
            result,
        });
        Ok(Some(variants::Case {
            name: case_name,
            major: args[group.arity - 1].clone(),
            branches,
            result,
        }))
    }
}
