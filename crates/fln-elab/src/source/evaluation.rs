//! An explicitly requested printer around one fully resolved evaluation term.
//! The retained transaction keeps original obligations and spent work intact;
//! neither this candidate nor its selected dictionary grants admission.
use super::*;
use fln_core::options::DataValue;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrintingError {
    MissingPrinter,
    MissingComponent(Name),
    MessageData,
    ProofOrType,
    UnsupportedOption(Name),
}

impl std::fmt::Display for PrintingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingPrinter => f.write_str(
                "#eval requires an existing Repr or ToString instance; automatic printer derivation is not implemented",
            ),
            Self::MissingComponent(name) => write!(
                f,
                "#eval printing requires the actual `{}` declaration",
                name.to_display_string(),
            ),
            Self::MessageData => f.write_str(
                "#eval printing through Lean.MessageData and its higher-priority ToExpr instances is not implemented",
            ),
            Self::ProofOrType => f.write_str(
                "#eval presentation of proofs, propositions and types is not implemented",
            ),
            Self::UnsupportedOption(name) => write!(
                f,
                "#eval presentation does not implement the selected `{}` option",
                name.to_display_string(),
            ),
        }
    }
}

fn error(reason: PrintingError) -> NatDefinitionElabError {
    failure(SourceInferenceError::EvaluationPrinting(reason))
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

/// `#guard e` (`syntax (name := guardCmd) "#guard " term : command`, Init/Guard.lean:127). The pin's
/// `evalGuardCmd` (Lean/Elab/Tactic/Guard.lean) elaborates `e` ensuring type `Bool`, where a
/// decidable proposition `p` becomes `Decidable.decide p` by coercion. It then evaluates the
/// result and fails unless it is `true`; the caller does that with the declaration built here.
fn guard_term(syntax: &Syntax, context: &mut Context) -> Result<Typed, NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Command", "guardCmd"]),
        2,
        "Lean.Parser.Command.guardCmd",
    )?;
    expect_atom(&parts[0], "#guard", "guard keyword")?;
    let bool_type = Expr::const_(name("Bool"), vec![]);
    let term = context.term(&parts[1], Some(bool_type.clone()))?;
    let type_ = context.whnf(&term.type_)?;
    let term = if type_ == bool_type {
        term
    } else if matches!(type_.node(), ExprNode::Sort { level } if level.is_zero()) {
        // `decPropToBool` (Init/Coe.lean): the proposition is decided.
        let dictionary = context.decision_dictionary(&term.value)?;
        Typed {
            value: Expr::app(Expr::app(context.decide_constant(), term.value), dictionary),
            type_: bool_type,
        }
    } else {
        return Err(failure(SourceInferenceError::ExpectedType));
    };
    let term = context.finish(term)?;
    context.check_compiled_recursors(&term)?;
    Ok(term)
}

/// One closed, fully resolved but unadmitted `#eval` candidate. Its original
/// context stays private so selecting a printer cannot refund elaboration work
/// or lose obligations. The caller may inspect its type to preserve IO handling,
/// then choose exactly one candidate and submit it to ordinary admission.
pub struct PreparedEvaluation {
    name: Name,
    context: Context,
    term: Typed,
    safety: DefinitionSafety,
}

/// An unadmitted action whose successful result is either silent Unit or a
/// checked Format. The caller must still admit and execute the declaration.
pub enum PreparedIoEvaluation {
    Unit(Declaration),
    Format(Declaration),
}

impl PreparedEvaluation {
    pub fn new(
        syntax: &Syntax,
        generated_name: Name,
        environment: &Environment,
        budget: Budget,
        scope: &SourceScope,
    ) -> Result<Self, NatDefinitionElabError> {
        let mut context = Context::scoped(environment, budget, scope);
        let guard = syntax.kind() == Some(&parser_kind(&["Command", "guardCmd"]));
        let term = if guard {
            guard_term(syntax, &mut context).and_then(|term| {
                context.publish_deprecated_uses()?;
                Ok(term)
            })
        } else {
            query_term(syntax, &generated_name, &mut context, true).map(|(term, _, _)| term)
        }
        .map_err(|error| with_pin_unknown_name_wording(error, environment))?;
        Ok(Self {
            name: generated_name,
            context,
            term,
            // BuiltinEvalCommand.addAndCompileExprForEval uses an unsafe
            // temporary definition. #guard's evalExpr remains safe. Every
            // candidate still passes ordinary council admission.
            safety: if guard {
                DefinitionSafety::Safe
            } else {
                DefinitionSafety::Unsafe
            },
        })
    }

    pub fn type_(&self) -> &Expr {
        &self.term.type_
    }

    /// Retain the original evaluation candidate without adding a printer.
    pub fn into_raw(self) -> Declaration {
        query_declaration(self.name, self.term, Vec::new(), self.safety)
    }

    /// Use the pin's Init-level order: `repr value`, then
    /// `Std.Format.text (ToString.toString value)`. Each application retains
    /// the original expression exactly once. Missing printers remain explicit
    /// refusals; this does not silently derive or invent an instance.
    pub fn into_format(mut self) -> Result<Declaration, NatDefinitionElabError> {
        let result = self.format_value()?;
        self.context.check_compiled_recursors(&result)?;
        Ok(query_declaration(
            self.name,
            result,
            Vec::new(),
            self.safety,
        ))
    }

    /// Map the selected printer over one already resolved IO action, using its
    /// canonical checked monad rather than inferring a Reader functor from an
    /// exposed world-token arrow. This constructs ordinary `Functor.map` code;
    /// no action is executed during selection, and its original expression
    /// occurs exactly once in the resulting declaration.
    pub fn into_io_presentation(
        mut self,
        monad: Expr,
        payload: Expr,
    ) -> Result<PreparedIoEvaluation, NatDefinitionElabError> {
        let monad_type = self
            .context
            .known_type(&monad)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let payload_type = self
            .context
            .known_type(&payload)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let action_type = self.context.match_apply(
            Typed {
                value: monad.clone(),
                type_: monad_type.clone(),
            },
            Typed {
                value: payload.clone(),
                type_: payload_type,
            },
        )?;
        self.context
            .constrain_type(&self.term.type_, &action_type.value)?;
        self.context.flush(true)?;

        let unit_name = name("Unit");
        if self.context.txn.env.contains(&unit_name) {
            let unit = self.context.constant(&unit_name)?;
            if self.context.defeq_guarded(&payload, &unit.value)? {
                // The pin's monadic Unit branch does not ask for any printer
                // and ignores options that only affect a printed value.
                return Ok(PreparedIoEvaluation::Unit(self.into_raw()));
            }
        }

        let original = self.term.clone();
        let saved_locals = self.context.txn.lctx.clone();
        let id = FVarId(self.context.fresh_name()?);
        self.context.txn.lctx.add_param(
            id.clone(),
            Name::anonymous(),
            payload.clone(),
            BinderInfo::Default,
        );
        self.term = Typed {
            value: Expr::fvar(id.clone()),
            type_: payload.clone(),
        };
        let printed = self.format_value()?;
        let printer = Typed {
            value: Expr::lam(
                Name::anonymous(),
                payload.clone(),
                printed
                    .value
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            ),
            type_: Expr::forall_e(
                Name::anonymous(),
                payload,
                printed
                    .type_
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            ),
        };
        self.context.txn.lctx = saved_locals;
        self.term = original.clone();

        let map_name = name("Functor.map");
        if !self.context.txn.env.contains(&map_name) {
            return Err(error(PrintingError::MissingComponent(map_name)));
        }
        let map = self.context.constant(&map_name)?;
        // Its first implicit argument is fixed explicitly. In particular,
        // normalizing `IO A` to its arrow cannot redirect instance selection.
        let map = self.context.match_apply(
            map,
            Typed {
                value: monad.clone(),
                type_: monad_type,
            },
        )?;
        let map = self
            .context
            .insert_implicits(map, ImplicitInsertion::ExplicitArgument)?;
        let map = self.context.match_apply(map, printer)?;
        let result = self.context.match_apply(map, original)?;
        let result = self.context.finish(result)?;
        let expected = Expr::app(monad, Expr::const_(name("Std.Format"), Vec::new()));
        self.context.constrain_type(&result.type_, &expected)?;
        self.context.flush(true)?;
        self.context.check_compiled_recursors(&result)?;
        Ok(PreparedIoEvaluation::Format(query_declaration(
            self.name,
            result,
            Vec::new(),
            self.safety,
        )))
    }

    fn format_value(&mut self) -> Result<Typed, NatDefinitionElabError> {
        if self
            .context
            .txn
            .env
            .contains(&name("Lean.MessageData.ofFormat"))
        {
            return Err(error(PrintingError::MessageData));
        }
        for (option, supported) in [
            ("format.width", DataValue::OfNat(120)),
            ("eval.type", DataValue::OfBool(false)),
        ] {
            let option = name(option);
            if self
                .context
                .txn
                .options
                .find(&option)
                .is_some_and(|value| value != &supported)
            {
                return Err(error(PrintingError::UnsupportedOption(option)));
            }
        }
        let type_ = self.context.whnf(&self.term.type_)?;
        let sort = self.context.known_type(&self.term.type_)?;
        if matches!(type_.node(), ExprNode::Sort { .. })
            || sort.as_ref().is_some_and(
                |sort| matches!(sort.node(), ExprNode::Sort { level } if level.is_zero()),
            )
        {
            return Err(error(PrintingError::ProofOrType));
        }
        let result = if let Some(repr) = self.try_printer("Repr", "repr")? {
            repr
        } else if let Some(string) = self.try_printer("ToString", "ToString.toString")? {
            let text_name = name("Std.Format.text");
            if !self.context.txn.env.contains(&text_name) {
                return Err(error(PrintingError::MissingComponent(text_name)));
            }
            let text = self.context.constant(&text_name)?;
            let result = self.context.match_apply(text, string)?;
            self.context.finish(result)?
        } else {
            return Err(error(PrintingError::MissingPrinter));
        };
        let format_name = name("Std.Format");
        if !self.context.txn.env.contains(&format_name) {
            return Err(error(PrintingError::MissingComponent(format_name)));
        }
        let format = self.context.constant(&format_name)?;
        self.context.constrain_type(&result.type_, &format.value)?;
        Ok(result)
    }

    fn try_printer(
        &mut self,
        class: &str,
        function: &str,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if !self.context.txn.env.contains(&name(class)) {
            return Ok(None);
        }
        let function = name(function);
        if !self.context.txn.env.contains(&function) {
            return Err(error(PrintingError::MissingComponent(function)));
        }
        let original = self.term.clone();
        let mut carrier = original.type_.clone();
        loop {
            self.context.tick()?;
            let saved = self.context.clone();
            let attempted = (|| {
                let function = self.context.constant(&function)?;
                let function = self
                    .context
                    .insert_implicits(function, ImplicitInsertion::ExplicitArgument)?;
                self.context.constrain_type(&original.type_, &carrier)?;
                let result = self.context.match_apply(
                    function,
                    Typed {
                        value: original.value.clone(),
                        type_: carrier.clone(),
                    },
                )?;
                self.context.finish(result)
            })();
            match attempted {
                Ok(result) => return Ok(Some(result)),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::InstanceSynthesisRequired,
                )) => {
                    let spent = self.context.txn.budget.heartbeats_consumed;
                    self.context = saved;
                    self.context.txn.budget.heartbeats_consumed = spent;
                    // `mkDeltaInstProj` also unfolds the carrier when ordinary
                    // instance selection cannot find its printer. The value
                    // remains unchanged and its type conversion is checked.
                    let reduced = self.context.whnf(&carrier)?;
                    if reduced == carrier {
                        return Ok(None);
                    }
                    carrier = reduced;
                }
                Err(error) => return Err(error),
            }
        }
    }
}
