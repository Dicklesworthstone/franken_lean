//! Constructor equality reasoning using only admitted recursors and Eq.rec.
//!
//! A field selector maps every other constructor to the actual left field as
//! a fallback. A discriminator maps the left constructor to T -> T and the
//! right constructor to T. Transporting identity along the supplied equality
//! then proves T. No no-confusion axiom, guessed equality, or checking shortcut
//! is introduced. Proof-valued families are deliberately excluded.
use super::*;
use fln_env::constants::{ConstantInfo, InductiveVal, RecursorVal};
use std::collections::HashSet;

struct Family {
    type_: Expr,
    family: InductiveVal,
    recursor: RecursorVal,
    levels: Vec<Level>,
    parameters: Vec<Expr>,
    indices: Vec<Expr>,
}
struct Constructor {
    name: Name,
    fields: Vec<Typed>,
}
enum Selection<'a> {
    Empty,
    Field {
        ctor: &'a Name,
        index: usize,
        fallback: &'a Expr,
    },
    FieldType {
        ctor: &'a Name,
        index: usize,
        fallback: &'a Expr,
    },
    Tag {
        ctor: &'a Name,
        selected: &'a Expr,
        other: &'a Expr,
    },
}

impl Context {
    fn equality_spine(&mut self, term: &Expr) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = self.whnf(term)?;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                _ => break,
            }
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    fn reasoning_family(
        &mut self,
        alpha: &Expr,
        data_only: bool,
    ) -> Result<Option<Family>, NatDefinitionElabError> {
        let type_ = self.whnf(alpha)?;
        let (head, mut arguments) = self.equality_spine(&type_)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.is_reflexive
            || family.num_nested != 0
            || family.all != [name.clone()]
            || levels.len() != family.base.level_params.len()
            || arguments.len() != family.num_params as usize + family.num_indices as usize
        {
            return Ok(None);
        }
        let Some(sort) = self.known_type(&type_)? else {
            return Ok(None);
        };
        if data_only
            && self.sort_level(&Typed {
                value: type_.clone(),
                type_: sort,
            })? == Level::zero()
        {
            return Ok(None);
        }
        let Some(ConstantInfo::Rec(recursor)) =
            self.txn.env.find(&Name::str(name.clone(), "rec")).cloned()
        else {
            return Ok(None);
        };
        // Selecting a type through a proof-only eliminator is not permissible.
        if recursor.is_unsafe
            || recursor.all != family.all
            || recursor.num_motives != 1
            || recursor.num_params != family.num_params
            || recursor.num_indices != family.num_indices
            || recursor.num_minors as usize != family.ctors.len()
            || recursor.rules.len() != family.ctors.len()
            || recursor.base.level_params.len() != levels.len() + 1
            || recursor.base.level_params[1..] != family.base.level_params
        {
            return Ok(None);
        }
        let indices = arguments.split_off(family.num_params as usize);
        Ok(Some(Family {
            type_,
            family,
            recursor,
            levels: levels.clone(),
            parameters: arguments,
            indices,
        }))
    }

    /// Open exactly one expected binder under a fresh identity. Result-function
    /// binders must not be mistaken for constructor fields or recursor hypotheses.
    fn equality_open(&mut self, type_: &mut Expr) -> Result<LocalDecl, NatDefinitionElabError> {
        let exposed = self.whnf(type_)?;
        let ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } = exposed.node()
        else {
            return Err(error(TacticError::ConstructorEquality));
        };
        let mut local = self.equality_local(binder_type.clone())?;
        local.binder_info = *binder_info;
        local.index = self.txn.lctx.len();
        eliminate::add_local(&mut self.txn.lctx, &local);
        *type_ = self.substitute(body, &Expr::fvar(local.id.clone()))?;
        Ok(local)
    }

    fn equality_apply(
        &mut self,
        function: Typed,
        value: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let type_ = self.whnf(&function.type_)?;
        let ExprNode::ForallE { body, .. } = type_.node() else {
            return Err(error(TacticError::ConstructorEquality));
        };
        Ok(Typed {
            type_: self.substitute(body, &value)?,
            value: Expr::app(function.value, value),
        })
    }

    fn equality_constructor(
        &mut self,
        term: &Expr,
        family: &Family,
    ) -> Result<Option<Constructor>, NatDefinitionElabError> {
        let (mut head, mut arguments) = self.equality_spine(term)?;
        if let ExprNode::Lit {
            literal: Literal::Nat(n),
        } = head.node()
            && arguments.is_empty()
            && family.family.base.name == Name::from_components(["Nat"])
            && family.levels.is_empty()
            && family.parameters.is_empty()
            && family.indices.is_empty()
        {
            if n.limbs_le().is_empty() {
                head = Expr::const_(Name::from_components(["Nat", "zero"]), Vec::new());
            } else {
                for _ in n.limbs_le() {
                    self.tick()?;
                }
                let previous = fln_bignum::nat::BigNatView::from_limbs_le(n.limbs_le())
                    .sub(fln_bignum::nat::BigNatView::from_limbs_le(&[1]));
                arguments.push(Expr::lit(Literal::Nat(
                    fln_bignum::interop::literal_from_bignat(&previous),
                )));
                head = Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new());
            }
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if ctor.is_unsafe
            || ctor.induct != family.family.base.name
            || !family.family.ctors.contains(name)
            || ctor.num_params != family.family.num_params
            || levels != &family.levels
            || arguments.len() != ctor.num_params as usize + ctor.num_fields as usize
        {
            return Ok(None);
        }
        let mut type_ =
            self.instantiate_params(&ctor.base.type_, &ctor.base.level_params, levels)?;
        let mut fields = Vec::new();
        for (i, value) in arguments.into_iter().enumerate() {
            let exposed = self.whnf(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = exposed.node()
            else {
                return Ok(None);
            };
            if i >= ctor.num_params as usize {
                fields.push(Typed {
                    value: value.clone(),
                    type_: binder_type.clone(),
                });
            }
            type_ = self.substitute(body, &value)?;
        }
        Ok(Some(Constructor {
            name: name.clone(),
            fields,
        }))
    }

    /// Build an index-generalized recursor function returning a fixed codomain.
    /// Only a selector whose chosen field really has that fixed type is usable;
    /// dependencies on other constructor fields are never silently erased.
    fn equality_selector(
        &mut self,
        family: &Family,
        codomain: &Expr,
        selection: Selection<'_>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        Ok(self
            .equality_selector_general(family, codomain, selection, None)?
            .map(|function| family.indices.iter().cloned().fold(function, Expr::app)))
    }

    /// Return a selector still generalized over its indices. The value selector
    /// can use a separately constructed type selector as its dependent motive.
    fn equality_selector_general(
        &mut self,
        family: &Family,
        codomain: &Expr,
        selection: Selection<'_>,
        motive: Option<Expr>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = self.equality_selector_inner(family, codomain, selection, motive);
        self.txn.lctx = saved;
        result
    }

    fn equality_selector_inner(
        &mut self,
        family: &Family,
        codomain: &Expr,
        selection: Selection<'_>,
        dependent_motive: Option<Expr>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(type_) = self.known_type(codomain)? else {
            return Ok(None);
        };
        let universe = self.sort_level(&Typed {
            value: codomain.clone(),
            type_,
        })?;
        let mut levels = vec![universe];
        levels.extend(family.levels.iter().cloned());
        let rec = &family.recursor;
        let mut function = Typed {
            value: Expr::const_(rec.base.name.clone(), levels.clone()),
            type_: self.instantiate_params(&rec.base.type_, &rec.base.level_params, &levels)?,
        };
        for param in &family.parameters {
            function = self.equality_apply(function, param.clone())?;
        }
        let ty = self.whnf(&function.type_)?;
        let ExprNode::ForallE { binder_type, .. } = ty.node() else {
            return Ok(None);
        };
        let saved = self.txn.lctx.clone();
        let motive = if let Some(motive) = dependent_motive {
            motive
        } else {
            let mut motive_type = binder_type.clone();
            let mut binders = Vec::new();
            for _ in 0..=family.family.num_indices {
                binders.push(self.equality_open(&mut motive_type)?);
            }
            let mut motive = codomain.clone();
            for binder in binders.iter().rev() {
                motive = self.close_equality_binder(binder, motive, true)?;
            }
            motive
        };
        self.txn.lctx = saved.clone();
        function = self.equality_apply(function, motive)?;
        let mut seen = HashSet::new();
        for rule in &rec.rules {
            self.tick()?;
            if !family.family.ctors.contains(&rule.ctor) || !seen.insert(rule.ctor.clone()) {
                return Ok(None);
            }
            let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&rule.ctor).cloned() else {
                return Ok(None);
            };
            if ctor.is_unsafe
                || ctor.induct != family.family.base.name
                || ctor.num_fields != rule.nfields
            {
                return Ok(None);
            }
            self.txn.lctx = saved.clone();
            let ty = self.whnf(&function.type_)?;
            let ExprNode::ForallE { binder_type, .. } = ty.node() else {
                return Ok(None);
            };
            let mut minor_type = binder_type.clone();
            let mut binders = Vec::new();
            let mut recursive = 0;
            for _ in 0..ctor.num_fields {
                let field = self.equality_open(&mut minor_type)?;
                if self.direct_match_field(&field.type_, &family.type_, &ctor.induct)? {
                    recursive += 1;
                }
                binders.push(field);
            }
            let value = match &selection {
                Selection::Empty => return Ok(None),
                Selection::Field { ctor, index, .. } if *ctor == &rule.ctor => {
                    let Some(field) = binders.get(*index) else {
                        return Ok(None);
                    };
                    Expr::fvar(field.id.clone())
                }
                Selection::FieldType { ctor, index, .. } if *ctor == &rule.ctor => {
                    let Some(field) = binders.get(*index) else {
                        return Ok(None);
                    };
                    field.type_.clone()
                }
                Selection::Field { fallback, .. } | Selection::FieldType { fallback, .. } => {
                    (*fallback).clone()
                }
                Selection::Tag {
                    ctor,
                    selected,
                    other,
                } => {
                    if *ctor == &rule.ctor {
                        (*selected).clone()
                    } else {
                        (*other).clone()
                    }
                }
            };
            for _ in 0..recursive {
                binders.push(self.equality_open(&mut minor_type)?);
            }
            // Compare only after opening the hypotheses: the minor result can
            // be a computation of the type selector on this constructor.
            let Some(actual_type) = self.known_type(&value)? else {
                return Ok(None);
            };
            let actual_type = self.whnf(&actual_type)?;
            let expected_type = self.whnf(&minor_type)?;
            if !self.proof_types_match(&actual_type, &expected_type)? {
                return Ok(None);
            }
            let mut minor = value;
            for binder in binders.iter().rev() {
                minor = self.close_equality_binder(binder, minor, true)?;
            }
            self.txn.lctx = saved.clone();
            function = self.equality_apply(function, minor)?;
        }
        Ok(Some(function.value))
    }

    /// Transport a supplied proof, not a fabricated equality, through a type
    /// family. The equality witness binder stays explicit even when unused.
    fn equality_transport(
        &mut self,
        equality: &Typed,
        codomain: &Expr,
        base: Expr,
        universe: Level,
    ) -> Result<Expr, NatDefinitionElabError> {
        let target = self.whnf(&equality.type_)?;
        let (level, alpha, left, right) =
            equality_target(&target).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let endpoint = self.equality_local(alpha.clone())?;
        let witness = self.equality_local(equality::equation(
            level.clone(),
            alpha.clone(),
            left.clone(),
            Expr::fvar(endpoint.id.clone()),
        ))?;
        let result = Expr::app(codomain.clone(), Expr::fvar(endpoint.id.clone()));
        let result = self.close_equality_binder(&witness, result, true)?;
        let motive = self.close_equality_binder(&endpoint, result, true)?;
        Ok([alpha, left, motive, base, right, equality.value.clone()]
            .into_iter()
            .fold(
                Expr::const_(Name::from_components(["Eq", "rec"]), vec![universe, level]),
                Expr::app,
            ))
    }

    fn constructor_clash(
        &mut self,
        equality: &Typed,
        family: &Family,
        right: &Name,
        target: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(type_) = self.known_type(target)? else {
            return Ok(None);
        };
        let universe = self.sort_level(&Typed {
            value: target.clone(),
            type_,
        })?;
        let local = self.equality_local(target.clone())?;
        let identity_type = self.close_equality_binder(&local, target.clone(), false)?;
        let identity = self.close_equality_binder(&local, Expr::fvar(local.id.clone()), true)?;
        let Some(selector) = self.equality_selector(
            family,
            &Expr::sort(universe.clone()),
            Selection::Tag {
                ctor: right,
                selected: target,
                other: &identity_type,
            },
        )?
        else {
            return Ok(None);
        };
        Ok(Some(self.equality_transport(
            equality, &selector, identity, universe,
        )?))
    }

    fn constructor_field_equality(
        &mut self,
        equality: &Typed,
        family: &Family,
        left: &Constructor,
        right: &Constructor,
        index: usize,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let field = &left.fields[index];
        let other = &right.fields[index];
        if !self.proof_types_match(&field.type_, &other.type_)? {
            return self.dependent_constructor_field_equality(equality, family, left, right, index);
        }
        let Some(selector) = self.equality_selector(
            family,
            &field.type_,
            Selection::Field {
                ctor: &left.name,
                index,
                fallback: &field.value,
            },
        )?
        else {
            let Some(mut derived) =
                self.dependent_constructor_field_equality(equality, family, left, right, index)?
            else {
                return Ok(None);
            };
            // The domains were checked convertible above. Eq's admitted K rule
            // makes this cast the identity; keep its evidence in the value and
            // expose the useful homogeneous equation to later tactics.
            let Some(type_) = self.known_type(&field.type_)? else {
                return Ok(None);
            };
            let level = self.sort_level(&Typed {
                value: field.type_.clone(),
                type_,
            })?;
            derived.type_ = equality::equation(
                level,
                field.type_.clone(),
                field.value.clone(),
                other.value.clone(),
            );
            return Ok(Some(derived));
        };
        let Some(type_) = self.known_type(&field.type_)? else {
            return Ok(None);
        };
        let universe = self.sort_level(&Typed {
            value: field.type_.clone(),
            type_,
        })?;
        let endpoint = self.equality_local(family.type_.clone())?;
        let equation = equality::equation(
            universe.clone(),
            field.type_.clone(),
            field.value.clone(),
            Expr::app(selector, Expr::fvar(endpoint.id.clone())),
        );
        let motive = self.close_equality_binder(&endpoint, equation, true)?;
        let base =
            equality::reflexivity(universe.clone(), field.type_.clone(), field.value.clone());
        Ok(Some(Typed {
            value: self.equality_transport(equality, &motive, base, Level::zero())?,
            type_: equality::equation(
                universe,
                field.type_.clone(),
                field.value.clone(),
                other.value.clone(),
            ),
        }))
    }

    /// Congruence under a nondependent function, retaining the supplied evidence.
    fn selector_congruence(
        &mut self,
        equality: &Typed,
        codomain: &Expr,
        universe: &Level,
        selector: &Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let type_ = self.whnf(&equality.type_)?;
        let (_, alpha, left, right) =
            equality_target(&type_).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let selected_left = Expr::app(selector.clone(), left);
        let selected_right = Expr::app(selector.clone(), right);
        let endpoint = self.equality_local(alpha)?;
        let result = equality::equation(
            universe.clone(),
            codomain.clone(),
            selected_left.clone(),
            Expr::app(selector.clone(), Expr::fvar(endpoint.id.clone())),
        );
        let motive = self.close_equality_binder(&endpoint, result, true)?;
        let base = equality::reflexivity(universe.clone(), codomain.clone(), selected_left.clone());
        Ok(Typed {
            value: self.equality_transport(equality, &motive, base, Level::zero())?,
            type_: equality::equation(
                universe.clone(),
                codomain.clone(),
                selected_left,
                selected_right,
            ),
        })
    }

    /// Cast through an equality of types using the identity type family. This
    /// is an ordinary Eq.rec, including its actual type-equality evidence.
    fn cast_constructor_field(
        &mut self,
        type_equality: &Typed,
        value: Expr,
        universe: &Level,
    ) -> Result<Expr, NatDefinitionElabError> {
        let type_local = self.equality_local(Expr::sort(universe.clone()))?;
        let motive =
            self.close_equality_binder(&type_local, Expr::fvar(type_local.id.clone()), true)?;
        self.equality_transport(type_equality, &motive, value, universe.clone())
    }

    /// A dependent field cannot be extracted with a constant-codomain selector.
    /// Instead construct a type selector D and a value selector d : (x : F) -> D x.
    /// Equality induction gives cast (congrArg D h) (d left) = d right. The cast
    /// remains in the hypothesis unless checked conversion can eliminate it;
    /// in particular, values of unrelated types are never compared directly.
    fn dependent_constructor_field_equality(
        &mut self,
        equality: &Typed,
        family: &Family,
        left: &Constructor,
        right: &Constructor,
        index: usize,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let field = &left.fields[index];
        let other = &right.fields[index];
        let Some(type_) = self.known_type(&field.type_)? else {
            return Ok(None);
        };
        let universe = self.sort_level(&Typed {
            value: field.type_.clone(),
            type_,
        })?;
        if universe == Level::zero() {
            return Ok(None);
        }
        let Some(type_) = self.known_type(&other.type_)? else {
            return Ok(None);
        };
        if self.sort_level(&Typed {
            value: other.type_.clone(),
            type_,
        })? != universe
        {
            return Ok(None);
        }
        let sort = Expr::sort(universe.clone());
        let Some(general_type_selector) = self.equality_selector_general(
            family,
            &sort,
            Selection::FieldType {
                ctor: &left.name,
                index,
                fallback: &field.type_,
            },
            None,
        )?
        else {
            return Ok(None);
        };
        let Some(general_value_selector) = self.equality_selector_general(
            family,
            &field.type_,
            Selection::Field {
                ctor: &left.name,
                index,
                fallback: &field.value,
            },
            Some(general_type_selector.clone()),
        )?
        else {
            return Ok(None);
        };
        let type_selector = family
            .indices
            .iter()
            .cloned()
            .fold(general_type_selector, Expr::app);
        let value_selector = family
            .indices
            .iter()
            .cloned()
            .fold(general_value_selector, Expr::app);
        let target = self.whnf(&equality.type_)?;
        let (family_level, _, left_endpoint, right_endpoint) =
            equality_target(&target).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let endpoint = self.equality_local(family.type_.clone())?;
        let endpoint_value = Expr::fvar(endpoint.id.clone());
        let witness = self.equality_local(equality::equation(
            family_level.clone(),
            family.type_.clone(),
            left_endpoint.clone(),
            endpoint_value.clone(),
        ))?;
        let abstract_equality = Typed {
            value: Expr::fvar(witness.id.clone()),
            type_: witness.type_.clone(),
        };
        let sort_universe = universe
            .clone()
            .succ()
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let type_equality =
            self.selector_congruence(&abstract_equality, &sort, &sort_universe, &type_selector)?;
        let selected_left = Expr::app(value_selector.clone(), left_endpoint.clone());
        let transported =
            self.cast_constructor_field(&type_equality, selected_left.clone(), &universe)?;
        let motive_result = equality::equation(
            universe.clone(),
            Expr::app(type_selector.clone(), endpoint_value.clone()),
            transported,
            Expr::app(value_selector.clone(), endpoint_value),
        );
        let motive = self.close_equality_binder(&witness, motive_result, true)?;
        let motive = self.close_equality_binder(&endpoint, motive, true)?;
        let base = equality::reflexivity(
            universe.clone(),
            Expr::app(type_selector.clone(), left_endpoint.clone()),
            selected_left.clone(),
        );
        let value = [
            family.type_.clone(),
            left_endpoint,
            motive,
            base,
            right_endpoint,
            equality.value.clone(),
        ]
        .into_iter()
        .fold(
            Expr::const_(
                Name::from_components(["Eq", "rec"]),
                vec![Level::zero(), family_level],
            ),
            Expr::app,
        );
        let actual_type_equality =
            self.selector_congruence(equality, &sort, &sort_universe, &type_selector)?;
        let transported =
            self.cast_constructor_field(&actual_type_equality, selected_left, &universe)?;
        Ok(Some(Typed {
            value,
            type_: equality::equation(
                universe,
                other.type_.clone(),
                transported,
                other.value.clone(),
            ),
        }))
    }

    pub(super) fn inject_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, Syntax::Ident { val: name, .. }, names] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "injection", "constructor equality tactic")?;
        let with_names = expect_null_args(names, "injection with")?;
        let rows = match with_names {
            [] => &[][..],
            [with, names] => {
                expect_atom(with, "with", "injection names")?;
                expect_null_args(names, "injection names")?
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        for row in rows {
            let name = match row {
                Syntax::Ident { val, .. } if seen.insert(val.clone()) => val.clone(),
                Syntax::Atom { val, .. } if val == "_" => Name::anonymous(),
                _ => return Err(error(TacticError::MalformedScript)),
            };
            names.push(name);
        }
        self.resolve_instances(false)?;
        self.flush(false)?;
        let local = goal
            .lctx
            .find_by_user_name(name)
            .cloned()
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        let equality = self
            .homogeneous_equality_evidence(&Typed {
                value: Expr::fvar(local.id),
                type_: local.type_,
            })?
            .ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let type_ = equality.type_.clone();
        let (_, alpha, lhs, rhs) =
            equality_target(&type_).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let family = self
            .reasoning_family(&alpha, true)?
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        let left = self
            .equality_constructor(&lhs, &family)?
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        let right = self
            .equality_constructor(&rhs, &family)?
            .ok_or_else(|| error(TacticError::ConstructorEquality))?;
        if left.name != right.name {
            if !names.is_empty() {
                return Err(error(TacticError::ConstructorEquality));
            }
            let value = self
                .constructor_clash(&equality, &family, &right.name, &goal.target)?
                .ok_or_else(|| error(TacticError::ConstructorEquality))?;
            return self.close_proof_goal(goal, value);
        }
        let mut equalities = Vec::new();
        for i in 0..left.fields.len() {
            self.tick()?;
            if let Some(equality) =
                self.constructor_field_equality(&equality, &family, &left, &right, i)?
            {
                equalities.push(equality);
            }
        }
        if equalities.len() < left.fields.len() {
            // A dependent field cannot in general be projected into one fixed
            // result type. Retain every field in constructor order by passing
            // typed heterogeneous equalities to a checked continuation instead.
            return self.inject_dependent_proof_goal(proof, goal, &equality, &names);
        }
        if equalities.is_empty() || names.len() > equalities.len() {
            return Err(error(TacticError::ConstructorEquality));
        }
        for (i, equality) in equalities.into_iter().enumerate() {
            let id = FVarId(self.fresh_name()?);
            let name = names.get(i).cloned().unwrap_or_else(|| id.0.clone());
            self.txn
                .lctx
                .add_let(id.clone(), name, equality.type_, equality.value);
            goal.introduced
                .push(self.txn.lctx.find(&id).expect("inserted equality").clone());
        }
        goal.lctx = self.txn.lctx.clone();
        proof.work.push(Work::Goal(goal));
        Ok(())
    }
}

impl Context {
    fn empty_evidence(
        &mut self,
        evidence: &Typed,
        target: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(family) = self.reasoning_family(&evidence.type_, false)? else {
            return Ok(None);
        };
        if !family.family.ctors.is_empty() {
            return Ok(None);
        }
        Ok(self
            .equality_selector(&family, target, Selection::Empty)?
            .map(|function| Expr::app(function, evidence.value.clone())))
    }

    /// Unequal compact literals use the already admitted Nat.beq computation,
    /// rather than peeling an astronomically large chain of successor nodes.
    /// The resulting Bool equality is justified by Eq.rec and checked conversion.
    fn unequal_nat_literals(
        &mut self,
        equality: &Typed,
        alpha: &Expr,
        left: &Expr,
        right: &Expr,
        target: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (
            ExprNode::Lit {
                literal: Literal::Nat(a),
            },
            ExprNode::Lit {
                literal: Literal::Nat(b),
            },
        ) = (left.node(), right.node())
        else {
            return Ok(None);
        };
        for _ in a.limbs_le().iter().chain(b.limbs_le()) {
            self.tick()?;
        }
        if a == b || alpha != &Expr::const_(Name::from_components(["Nat"]), Vec::new()) {
            return Ok(None);
        }
        let bool_type = Expr::const_(Name::from_components(["Bool"]), Vec::new());
        let yes = Expr::const_(Name::from_components(["Bool", "true"]), Vec::new());
        let no = Expr::const_(Name::from_components(["Bool", "false"]), Vec::new());
        let compare = Expr::app(
            Expr::const_(Name::from_components(["Nat", "beq"]), Vec::new()),
            left.clone(),
        );
        let endpoint = self.equality_local(alpha.clone())?;
        let eq = equality::equation(
            Level::one(),
            bool_type.clone(),
            yes.clone(),
            Expr::app(compare, Expr::fvar(endpoint.id.clone())),
        );
        let motive = self.close_equality_binder(&endpoint, eq, true)?;
        let base = equality::reflexivity(Level::one(), bool_type.clone(), yes.clone());
        let proof = self.equality_transport(equality, &motive, base, Level::zero())?;
        let equation = Typed {
            value: proof,
            type_: equality::equation(Level::one(), bool_type.clone(), yes, no),
        };
        let Some(family) = self.reasoning_family(&bool_type, true)? else {
            return Ok(None);
        };
        self.constructor_clash(
            &equation,
            &family,
            &Name::from_components(["Bool", "false"]),
            target,
        )
    }

    pub(super) fn contradict_proof_goal(
        &mut self,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        self.resolve_instances(false)?;
        self.flush(false)?;
        let original: Vec<_> = goal
            .lctx
            .decls()
            .iter()
            .map(|local| Typed {
                value: Expr::fvar(local.id.clone()),
                type_: local.type_.clone(),
            })
            .collect();
        let mut pending: std::collections::VecDeque<_> = original.iter().cloned().collect();
        let mut negative = Vec::new();
        for local in &original {
            self.tick()?;
            let ty = self.whnf(&local.type_)?;
            if let ExprNode::ForallE {
                binder_type, body, ..
            } = ty.node()
            {
                negative.push((local.value.clone(), binder_type.clone(), body.clone()));
                // Reflexive equality is useful evidence even without a named
                // proof local. A failed conversion does not mutate the store.
                if let Some((level, alpha, left, right)) = equality_target(binder_type)
                    && self.proof_types_match(&left, &right)?
                {
                    let proof = equality::reflexivity(level, alpha, left);
                    let applied = Typed {
                        value: Expr::app(local.value.clone(), proof.clone()),
                        type_: self.substitute(body, &proof)?,
                    };
                    if let Some(result) = self.empty_evidence(&applied, &goal.target)? {
                        return self.close_proof_goal(goal, result);
                    }
                }
            }
        }
        let mut seen = HashSet::new();
        // Pin every pair whose identities are memoized for this request. A
        // dropped temporary allocation can never be reused as an existing key.
        let mut roots = Vec::new();
        while let Some(evidence) = pending.pop_front() {
            self.tick()?;
            if let Some(result) = self.empty_evidence(&evidence, &goal.target)? {
                return self.close_proof_goal(goal, result);
            }
            for (function, domain, body) in &negative {
                self.tick()?;
                if self.proof_types_match(&evidence.type_, domain)? {
                    let application = Typed {
                        value: Expr::app(function.clone(), evidence.value.clone()),
                        type_: self.substitute(body, &evidence.value)?,
                    };
                    if let Some(result) = self.empty_evidence(&application, &goal.target)? {
                        return self.close_proof_goal(goal, result);
                    }
                }
            }
            let Some(evidence) = self.homogeneous_equality_evidence(&evidence)? else {
                continue;
            };
            let type_ = evidence.type_.clone();
            let Some((_, alpha, left, right)) = equality_target(&type_) else {
                continue;
            };
            let alpha = self.whnf(&alpha)?;
            let left = self.whnf(&left)?;
            let right = self.whnf(&right)?;
            if !seen.insert((left.allocation_identity(), right.allocation_identity())) {
                continue;
            }
            roots.push((left.clone(), right.clone()));
            if let Some(result) =
                self.unequal_nat_literals(&evidence, &alpha, &left, &right, &goal.target)?
            {
                return self.close_proof_goal(goal, result);
            }
            let Some(family) = self.reasoning_family(&alpha, true)? else {
                continue;
            };
            let Some(left) = self.equality_constructor(&left, &family)? else {
                continue;
            };
            let Some(right) = self.equality_constructor(&right, &family)? else {
                continue;
            };
            if left.name != right.name {
                if let Some(result) =
                    self.constructor_clash(&evidence, &family, &right.name, &goal.target)?
                {
                    return self.close_proof_goal(goal, result);
                }
            } else {
                for index in 0..left.fields.len() {
                    self.tick()?;
                    if let Some(proof) =
                        self.constructor_field_equality(&evidence, &family, &left, &right, index)?
                    {
                        pending.push_back(proof);
                    }
                }
            }
        }
        Err(error(TacticError::NoContradiction))
    }
}
