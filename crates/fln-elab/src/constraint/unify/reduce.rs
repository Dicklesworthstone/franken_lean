//! Metered beta/delta/zeta/iota reduction for native unification.
//!
//! Eliminator majors use heap continuations rather than recursive calls. Only
//! registered, safe single-family recursors and initialized quotient primitives
//! reduce. A blocked major is rebuilt once; it is never re-entered in a loop.
//! This module has no declaration-publication authority. Assignment validation
//! and all-or-nothing publication remain in the parent solver.
mod quotient;

use super::*;
use fln_env::constants::RecursorVal;

enum Continuation {
    Quotient {
        head: Expr,
        arguments: Vec<Expr>,
        major: usize,
    },
    Projection {
        structure: Name,
        index: u64,
        arguments: Vec<Expr>,
    },
    Recursor {
        head: Expr,
        recursor: Box<RecursorVal>,
        arguments: Vec<Expr>,
        prefix: usize,
        major: usize,
    },
}

fn count(value: u32) -> Result<usize, UnificationError> {
    usize::try_from(value).map_err(|_| UnificationError::ExpressionScope)
}

fn recursor_positions(recursor: &RecursorVal) -> Result<(usize, usize), UnificationError> {
    let parameters = count(recursor.num_params)?;
    let motives = count(recursor.num_motives)?;
    let minors = count(recursor.num_minors)?;
    let prefix = parameters
        .checked_add(motives)
        .and_then(|n| n.checked_add(minors))
        .ok_or(UnificationError::ExpressionScope)?;
    let major = prefix
        .checked_add(count(recursor.num_indices)?)
        .ok_or(UnificationError::ExpressionScope)?;
    Ok((prefix, major))
}

impl Engine<'_> {
    pub(super) fn whnf(
        &mut self,
        expr: &Expr,
        locals: &LocalContext,
    ) -> Result<Expr, UnificationError> {
        let mut head = expr.clone();
        let mut args = Vec::new();
        let mut continuations = Vec::new();
        'reduce: loop {
            loop {
                self.meter.tick()?;
                match head.node() {
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        continuations.push(Continuation::Projection {
                            structure: struct_name.clone(),
                            index: *idx,
                            arguments: std::mem::take(&mut args),
                        });
                        head = expr.clone();
                    }
                    ExprNode::MData { expr, .. } => head = expr.clone(),
                    ExprNode::LetE { value, body, .. } => head = self.substitute(body, value)?,
                    ExprNode::App { f, a } => {
                        args.push(a.clone());
                        head = f.clone();
                    }
                    ExprNode::MVar { id } => {
                        if let Some(value) = self.work.mvars.get_assigned_expr(id) {
                            head = value.clone();
                        } else {
                            break;
                        }
                    }
                    ExprNode::FVar { id } if self.budget.zeta_delta => {
                        if let Some(value) = locals.find(id).and_then(|local| local.value.as_ref())
                        {
                            head = value.clone();
                        } else {
                            break;
                        }
                    }
                    ExprNode::Lam { body, .. } if !args.is_empty() => {
                        let argument = args.pop().expect("nonempty application spine");
                        head = self.substitute(body, &argument)?;
                    }
                    ExprNode::Const { name, levels } => match self.work.env.find(name) {
                        Some(ConstantInfo::Defn(definition))
                            if definition.safety == DefinitionSafety::Safe
                                && definition.base.level_params.len() == levels.len()
                                && match self.budget.transparency {
                                    UnificationTransparency::None => false,
                                    UnificationTransparency::Abbreviations => {
                                        definition.hints == ReducibilityHints::Abbrev
                                    }
                                    UnificationTransparency::SafeDefinitions => true,
                                } =>
                        {
                            let value = definition.value.clone();
                            let parameters = definition.base.level_params.clone();
                            self.scan(&value)?;
                            head = crate::universe::parameters::instantiate(
                                || self.meter.node(),
                                || UnificationError::ExpressionScope,
                                &value,
                                &parameters,
                                levels,
                            )?;
                        }
                        Some(ConstantInfo::Quot(_)) => {
                            let Some(major) = self.quotient_major_index(&head, args.len())? else {
                                break;
                            };
                            let value = args[args.len() - major - 1].clone();
                            continuations.push(Continuation::Quotient {
                                head,
                                arguments: std::mem::take(&mut args),
                                major,
                            });
                            head = value;
                        }
                        Some(ConstantInfo::Rec(recursor)) => {
                            // Iota is independent of delta transparency. Do not
                            // guess the layout of unsupported recursor families.
                            if recursor.is_unsafe
                                || recursor.num_motives != 1
                                || recursor.all.len() != 1
                                || recursor.base.level_params.len() != levels.len()
                            {
                                break;
                            }
                            let (prefix, major) = recursor_positions(recursor)?;
                            if major >= args.len() {
                                break;
                            }
                            // Charge metadata before cloning its proportional
                            // arrays; rule bodies themselves remain shared.
                            for _ in &recursor.rules {
                                self.meter.node()?;
                            }
                            for _ in &recursor.base.level_params {
                                self.meter.node()?;
                            }
                            let recursor = Box::new(recursor.clone());
                            let value = args[args.len() - major - 1].clone();
                            continuations.push(Continuation::Recursor {
                                head,
                                recursor,
                                arguments: std::mem::take(&mut args),
                                prefix,
                                major,
                            });
                            head = value;
                        }
                        _ => break,
                    },
                    _ => break,
                }
            }
            while let Some(continuation) = continuations.pop() {
                self.meter.tick()?;
                match continuation {
                    Continuation::Quotient {
                        head: eliminator,
                        arguments: mut outer,
                        major,
                    } => {
                        if let Some(result) =
                            self.quotient_step(&eliminator, &outer, &head, &args)?
                        {
                            // Preserve applications of a function-valued result.
                            outer.truncate(outer.len() - major - 1);
                            head = result;
                            args = outer;
                            continue 'reduce;
                        }
                        let position = outer.len() - major - 1;
                        outer[position] = self.rebuild_application(head, args)?;
                        head = eliminator;
                        args = outer;
                    }
                    Continuation::Projection {
                        structure,
                        index,
                        arguments: outer,
                    } => {
                        if let Some(field) = crate::records::constructor_field(
                            &self.work.env,
                            &structure,
                            index,
                            &head,
                            &args,
                        ) {
                            head = field;
                            args = outer;
                            continue 'reduce;
                        }
                        head = self.rebuild_application(head, args)?;
                        head = Expr::proj(structure, index, head);
                        args = outer;
                    }
                    Continuation::Recursor {
                        head: rec_head,
                        recursor,
                        arguments: mut outer,
                        prefix,
                        major,
                    } => {
                        if let Some(result) =
                            self.iota(&rec_head, &recursor, &outer, prefix, &head, &args)?
                        {
                            // The reversed spine starts with arguments after
                            // the major. Keep these for a function-valued result.
                            outer.truncate(outer.len() - major - 1);
                            head = result;
                            args = outer;
                            continue 'reduce;
                        }
                        let position = outer.len() - major - 1;
                        outer[position] = self.rebuild_application(head, args)?;
                        head = rec_head;
                        args = outer;
                    }
                }
                // Unwind blocked majors without resubmitting the same
                // expression to the reduction loop.
            }
            return self.rebuild_application(head, args);
        }
    }

    fn rebuild_application(
        &mut self,
        mut head: Expr,
        args: Vec<Expr>,
    ) -> Result<Expr, UnificationError> {
        for argument in args.into_iter().rev() {
            self.meter.tick()?;
            head = Expr::app(head, argument);
        }
        Ok(head)
    }

    fn iota(
        &mut self,
        rec_head: &Expr,
        recursor: &RecursorVal,
        arguments: &[Expr],
        prefix: usize,
        major_head: &Expr,
        major_arguments: &[Expr],
    ) -> Result<Option<Expr>, UnificationError> {
        // Earlier equations may have assigned universe metavariables. Resolve
        // them before checking compatibility, without assigning holes merely
        // to enable a reduction.
        let rec_head = self.instantiate(rec_head)?;
        let major_head = self.instantiate(major_head)?;
        let compact = self.nat_literal_major(recursor, &major_head, major_arguments)?;
        let (major_head, major_arguments) = match &compact {
            Some((head, arguments)) => (head, arguments.as_slice()),
            None => (&major_head, major_arguments),
        };
        let ExprNode::Const { levels, .. } = rec_head.node() else {
            return Ok(None);
        };
        let ExprNode::Const {
            name: constructor_name,
            levels: constructor_levels,
        } = major_head.node()
        else {
            return Ok(None);
        };
        let family_name = &recursor.all[0];
        let Some(ConstantInfo::Induct(family)) = self.work.env.find(family_name) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.num_indices != recursor.num_indices
            || family.num_nested != 0
            || family.num_params != recursor.num_params
            || family.all != recursor.all
            || count(recursor.num_minors)? != family.ctors.len()
            || recursor.rules.len() != family.ctors.len()
        {
            return Ok(None);
        }
        for _ in &family.ctors {
            self.meter.node()?;
        }
        for _ in &family.base.level_params {
            self.meter.node()?;
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.work.env.find(constructor_name) else {
            return Ok(None);
        };
        let params = count(ctor.num_params)?;
        let fields = count(ctor.num_fields)?;
        if ctor.is_unsafe
            || &ctor.induct != family_name
            || ctor.num_params != family.num_params
            || !family.ctors.contains(constructor_name)
            || ctor.base.level_params != family.base.level_params
            || ctor.base.level_params.len() != constructor_levels.len()
            || params.checked_add(fields) != Some(major_arguments.len())
        {
            return Ok(None);
        }
        let compatible = if recursor.base.level_params == family.base.level_params {
            levels == constructor_levels
        } else {
            recursor.base.level_params.len() == family.base.level_params.len() + 1
                && recursor.base.level_params[1..] == family.base.level_params
                && levels.len() == constructor_levels.len() + 1
                && levels[1..] == *constructor_levels
        };
        if !compatible {
            return Ok(None);
        }
        let mut selected = None;
        for rule in &recursor.rules {
            self.meter.node()?;
            if &rule.ctor == constructor_name {
                if count(rule.nfields)? != fields {
                    return Ok(None);
                }
                selected = Some(rule.rhs.clone());
                break;
            }
        }
        let Some(rhs) = selected else {
            return Ok(None);
        };
        self.scan(&rhs)?;
        let mut result = crate::universe::parameters::instantiate(
            || self.meter.node(),
            || UnificationError::ExpressionScope,
            &rhs,
            &recursor.base.level_params,
            levels,
        )?;
        for argument in arguments
            .iter()
            .rev()
            .take(prefix)
            .chain(major_arguments.iter().rev().skip(params))
        {
            self.meter.node()?;
            result = Expr::app(result, argument.clone());
        }
        Ok(Some(result))
    }

    /// Expose one constructor layer of a compact numeral, never a unary tree.
    /// The ordinary iota path still validates the recursor and selected rule.
    fn nat_literal_major(
        &mut self,
        recursor: &RecursorVal,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<(Expr, Vec<Expr>)>, UnificationError> {
        let ExprNode::Lit {
            literal: Literal::Nat(value),
        } = head.node()
        else {
            return Ok(None);
        };
        if !arguments.is_empty() || recursor.all != [Name::from_components(["Nat"])] {
            return Ok(None);
        }
        self.meter.tick()?;
        let Declaration::Inductive(seed) = crate::seed::nat_inductive_seed_declaration() else {
            unreachable!("the canonical Nat seed is inductive");
        };
        let index = usize::from(!value.limbs_le().is_empty());
        // A familiar-looking name is not evidence of Nat's constructor laws.
        if self.work.env.find(&seed.types[0].base.name)
            != Some(&ConstantInfo::Induct(seed.types[0].clone()))
            || self.work.env.find(&seed.ctors[index].base.name)
                != Some(&ConstantInfo::Ctor(seed.ctors[index].clone()))
        {
            return Ok(None);
        }
        let fields = if index == 0 {
            Vec::new()
        } else {
            for _ in value.limbs_le() {
                self.meter.node()?;
            }
            let previous = fln_bignum::nat::BigNatView::from_limbs_le(value.limbs_le())
                .sub(fln_bignum::nat::BigNatView::from_limbs_le(&[1]));
            vec![Expr::lit(Literal::Nat(
                fln_bignum::interop::literal_from_bignat(&previous),
            ))]
        };
        Ok(Some((
            Expr::const_(seed.ctors[index].base.name.clone(), Vec::new()),
            fields,
        )))
    }
}
