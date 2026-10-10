//! Apply only explicitly requested, exactly recognized IO evaluation entries.

use super::*;
use crate::source_evaluation::IoResultTypes;

#[derive(Clone, Copy)]
enum Family {
    Base,
    Io,
    Eio,
}

struct ActionType {
    family: Family,
    arguments: Vec<Expr>,
    aliases: Vec<Name>,
}

fn family(label: &Name) -> Option<(Family, usize)> {
    if label == &name("BaseIO") {
        Some((Family::Base, 1))
    } else if label == &name("IO") {
        Some((Family::Io, 1))
    } else if label == &name("EIO") {
        Some((Family::Eio, 2))
    } else {
        None
    }
}

impl Preparation<'_> {
    pub(crate) fn is_evaluation_action(&mut self, source: &Expr) -> Result<bool, IngressError> {
        self.evaluation_action_type(source)
            .map(|action| action.is_some())
    }

    fn checked_io_world(&mut self) -> Result<bool, IngressError> {
        self.tick()?;
        if !self.io_world_checked {
            if !source_intrinsics::io::io_world_contract_matches(
                self.environment,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(false);
            }
            self.io_world_checked = true;
        }
        Ok(true)
    }

    /// Keep the checked phantom state index stable. Delta-reducing it to its
    /// opaque Type-field projection would cause generic hidden-type erasure
    /// to substitute a boxed carrier in constructor results only. This grants
    /// no runtime representation or inhabitant to RealWorld itself.
    pub(super) fn preserve_io_world_type(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<bool, IngressError> {
        if !arguments.is_empty()
            || !matches!(head.node(), ExprNode::Const { name: label, levels }
                if label == &name("IO.RealWorld") && levels.is_empty())
        {
            return Ok(false);
        }
        self.checked_io_world()
    }

    /// Reduce only safe logical type aliases, stopping at the selected names.
    /// Runtime erasure must not turn distinct phantom world indices into one
    /// representation before entry selection has checked the logical type.
    fn evaluation_type_head(
        &mut self,
        source: &Expr,
        anchors: &[Name],
        aliases: &mut Vec<Name>,
    ) -> Result<(Expr, Vec<Expr>), IngressError> {
        let (mut head, mut arguments) = self.spine(source)?;
        arguments.reverse();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    reserve(&mut arguments, self.limits.max_application_args)?;
                    arguments.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::LetE { value, body, .. } => {
                    head = self.substitution(body, value)?;
                }
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    head = self.substitution(body, &arguments.pop().expect("type argument"))?;
                }
                ExprNode::Const { name, levels } => {
                    if anchors.contains(name) {
                        break;
                    }
                    let Some(ConstantInfo::Defn(definition)) = self.environment.find(name) else {
                        break;
                    };
                    if definition.safety != DefinitionSafety::Safe
                        || definition.base.level_params.len() != levels.len()
                    {
                        break;
                    }
                    reserve(aliases, self.limits.max_nodes)?;
                    aliases.push(name.clone());
                    head = self.universe_instance(
                        &definition.value.clone(),
                        &definition.base.level_params.clone(),
                        levels,
                    )?;
                }
                _ => break,
            }
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    fn is_io_state_type(
        &mut self,
        source: &Expr,
        aliases: &mut Vec<Name>,
    ) -> Result<bool, IngressError> {
        let expected = name("IO.RealWorld");
        let (head, arguments) =
            self.evaluation_type_head(source, std::slice::from_ref(&expected), aliases)?;
        Ok(arguments.is_empty()
            && matches!(head.node(), ExprNode::Const { name, levels }
                if name == &expected && levels.is_empty()))
    }

    /// The source elaborator may already expose IO's outer arrow. Match its
    /// complete logical world domain and result family before replacing any
    /// runtime type. An ST action at another state is not an IO evaluation.
    fn evaluation_action_type(
        &mut self,
        source: &Expr,
    ) -> Result<Option<ActionType>, IngressError> {
        let mut aliases = Vec::new();
        let (head, arguments) = self.evaluation_type_head(
            source,
            &[name("BaseIO"), name("IO"), name("EIO")],
            &mut aliases,
        )?;
        if let ExprNode::Const { name, levels } = head.node()
            && let Some((family, arity)) = family(name)
            && levels.is_empty()
            && arguments.len() == arity
        {
            return Ok(Some(ActionType {
                family,
                arguments,
                aliases,
            }));
        }
        let ExprNode::ForallE {
            binder_type, body, ..
        } = head.node()
        else {
            return Ok(None);
        };
        if !arguments.is_empty() || body.has_loose_bvars() {
            return Ok(None);
        }
        let void = name("Void");
        let (domain, domain_arguments) =
            self.evaluation_type_head(binder_type, std::slice::from_ref(&void), &mut aliases)?;
        if !matches!(domain.node(), ExprNode::Const { name, levels }
            if name == &void && levels.is_empty())
            || domain_arguments.len() != 1
            || !self.is_io_state_type(&domain_arguments[0], &mut aliases)?
        {
            return Ok(None);
        }
        let (result, arguments) = self.evaluation_type_head(body, &[], &mut aliases)?;
        let ExprNode::Const {
            name: label,
            levels,
        } = result.node()
        else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        let (family, state, arguments) = if label == &name("ST.Out") && arguments.len() == 2 {
            (
                Family::Base,
                arguments[0].clone(),
                vec![arguments[1].clone()],
            )
        } else if label == &name("EST.Out") && arguments.len() == 3 {
            (
                Family::Eio,
                arguments[1].clone(),
                vec![arguments[0].clone(), arguments[2].clone()],
            )
        } else {
            return Ok(None);
        };
        if !self.is_io_state_type(&state, &mut aliases)? {
            return Ok(None);
        }
        Ok(Some(ActionType {
            family,
            arguments,
            aliases,
        }))
    }

    /// Build a runtime-only action application after both checkers accepted
    /// the unchanged declaration. The token never becomes a logical argument
    /// to either checker, an environment constant, or a proof.
    pub(crate) fn evaluation_entry(
        &mut self,
        expression: &Expr,
        declared_type: &Expr,
    ) -> Result<Option<(Expr, Expr, IoResultTypes)>, IngressError> {
        let Some(ActionType {
            family,
            arguments,
            aliases,
        }) = self.evaluation_action_type(declared_type)?
        else {
            return Ok(None);
        };
        if !self.checked_io_world()? {
            return Ok(None);
        }
        let (value, error) = match family {
            Family::Base => (&arguments[0], None),
            Family::Io => (&arguments[0], Some(Expr::const_(name("IO.Error"), vec![]))),
            Family::Eio => {
                let error = self.normalize_type(&arguments[0])?;
                if error != Expr::const_(name("IO.Error"), vec![]) {
                    // The pin has no default MonadEval adapter for arbitrary
                    // EIO errors. A source EIO.toIO adapter remains ordinary
                    // checked code and produces a supported IO entry.
                    return Err(unsupported("#eval monad requires a checked IO adapter"));
                }
                (&arguments[1], Some(error))
            }
        };
        for alias in aliases {
            source_intrinsics::check_selected_extern_attribute(
                self.environment,
                &alias,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?;
        }
        let types = IoResultTypes {
            value: self.normalize_type(value)?,
            error: error
                .as_ref()
                .map(|error| self.normalize_type(error))
                .transpose()?,
        };
        let Some(world) = self.st_evaluation_world()? else {
            return Err(unsupported(
                "IO evaluation requires the checked ST world representation",
            ));
        };
        let runtime_type = self.normalize_type(declared_type)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = runtime_type.node()
        else {
            return Err(unsupported("checked IO entry is not an action"));
        };
        if binder_type != &world {
            return Err(unsupported(
                "checked IO entry has a different world representation",
            ));
        }
        if !matches!(self.value_type(&runtime_type)?, Some(ValueType::Closure(_))) {
            return Err(unsupported("checked IO entry runtime representation"));
        }
        let result_type = self.substitution(body, &proofs::erased_value())?;
        self.tick()?;
        let entry = Expr::let_e(
            name("_fln_runtime_io_evaluation_action"),
            declared_type.clone(),
            expression.clone(),
            Expr::app(
                Expr::bvar(0).map_err(|_| unsupported("IO evaluation action scope"))?,
                proofs::erased_value(),
            ),
            false,
        );
        Ok(Some((entry, result_type, types)))
    }
}
