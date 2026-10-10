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

/// One closed, fully resolved but unadmitted `#eval` candidate. Its original
/// context stays private so selecting a printer cannot refund elaboration work
/// or lose obligations. The caller may inspect its type to preserve IO handling,
/// then choose exactly one candidate and submit it to ordinary admission.
pub struct PreparedEvaluation {
    name: Name,
    context: Context,
    term: Typed,
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
        let (term, _) = query_term(syntax, &generated_name, &mut context, true)
            .map_err(|error| with_pin_unknown_name_wording(error, environment))?;
        Ok(Self {
            name: generated_name,
            context,
            term,
        })
    }

    pub fn type_(&self) -> &Expr {
        &self.term.type_
    }

    /// Retain the original evaluation candidate without adding a printer.
    pub fn into_raw(self) -> Declaration {
        query_declaration(self.name, self.term, Vec::new())
    }

    /// Use the pin's Init-level order: `repr value`, then
    /// `Std.Format.text (ToString.toString value)`. Each application retains
    /// the original expression exactly once. Missing printers remain explicit
    /// refusals; this does not silently derive or invent an instance.
    pub fn into_format(mut self) -> Result<Declaration, NatDefinitionElabError> {
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
        self.context.check_compiled_recursors(&result.value)?;
        Ok(query_declaration(self.name, result, Vec::new()))
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
