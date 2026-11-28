//! Imported `autoParam` tactics are quoted, safe `Lean.Syntax` values. Decode
//! their actual constructor data with the ordinary metered pure reducer, then
//! elaborate a normal `by` term. Neither imported code nor a theorem shortcut
//! executes here. The resulting proof still passes ordinary command admission.
use super::*;
use fln_env::constants::ConstantInfo;
use fln_syntax::source::BytePos;
use fln_syntax::tree::{Preresolved, RawIdentifier};

const MAX_AUTO_PARAM_DEPTH: usize = 8;

pub(in crate::source) struct AutoParameter {
    id: MVarId,
    tactic: Syntax,
}

impl AutoParameter {
    pub(in crate::source) fn value(&self) -> Expr {
        Expr::mvar(self.id.clone())
    }
}

fn invalid() -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax {
        expected: "closed quoted Lean.Syntax data for an autoParam tactic",
    }
}

impl Context {
    pub(in crate::source) fn defer_auto_parameter(
        &mut self,
        tactic: &Expr,
        domain: Expr,
    ) -> Result<AutoParameter, NatDefinitionElabError> {
        // `getAutoParamTactic?` requires a constant, not an arbitrary term
        // of type Syntax (Lean/Elab/App.lean:826-854).
        let ExprNode::Const { name, levels } = tactic.node() else {
            return Err(invalid());
        };
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Err(invalid());
        };
        if definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Err(invalid());
        }
        // The pin executes this constant when reading its quotation. A
        // runtime replacement would make its logical value insufficient.
        let environment = self.txn.env.clone();
        let externs = crate::externs::ExternTable::read_metered(&environment, |amount| {
            for _ in 0..amount {
                self.tick()?;
            }
            Ok(())
        })
        .map_err(|error| match error {
            crate::externs::ExternReadError::Registry(error) => {
                failure(SourceInferenceError::ExternJournal(error))
            }
            crate::externs::ExternReadError::Budget(error) => error,
        })?;
        let implementations =
            crate::implemented_by::ImplementedByTable::read_metered(&environment, |amount| {
                for _ in 0..amount {
                    self.tick()?;
                }
                Ok(())
            })
            .map_err(|error| match error {
                crate::implemented_by::ImplementedByReadError::Registry(error) => {
                    failure(SourceInferenceError::ImplementedByJournal(error))
                }
                crate::implemented_by::ImplementedByReadError::Budget(error) => error,
            })?;
        if externs.get(name).is_some() || implementations.get(name).is_some() {
            return Err(invalid());
        }
        let type_ = self.instantiate_params(
            &definition.base.type_,
            &definition.base.level_params,
            levels,
        )?;
        self.constrain_type(
            &type_,
            &Expr::const_(Name::from_components(["Lean", "Syntax"]), Vec::new()),
        )?;
        // The pin gives generated tactic definitions opaque reducibility
        // hints. Their safe value is the quotation, not an opaque proof body.
        let value =
            self.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
        let tactic = self.auto_param_syntax(value)?;
        let tactic = Syntax::node(
            parser_kind(&["Term", "byTactic"]),
            vec![Syntax::atom(SourceInfo::None, "by"), tactic],
        );
        let name = self.fresh_name()?;
        let id = MVarId(name.clone());
        self.txn.mvars.declare(
            id.clone(),
            name,
            domain,
            self.txn.lctx.clone(),
            MetavarKind::SyntheticOpaque,
            0,
            None,
        );
        Ok(AutoParameter { id, tactic })
    }

    /// Run defaults only after later arguments and the expected result have
    /// constrained their types, as for deferred `calc` proofs. Each proof sees
    /// its original scope, so a later eta parameter cannot capture a quote.
    pub(in crate::source) fn finish_auto_parameters(
        &mut self,
        parameters: Vec<AutoParameter>,
    ) -> Result<(), NatDefinitionElabError> {
        if parameters.is_empty() {
            return Ok(());
        }
        if self.auto_param_depth >= MAX_AUTO_PARAM_DEPTH {
            return Err(failure(SourceInferenceError::NativeEvaluationInconclusive(
                Box::new(
                    fln_core::outcome::Inconclusive::resource(fln_core::outcome::ResourceUsage {
                        reason: fln_core::diag::ResourceReason::RecursionDepth {
                            limit: MAX_AUTO_PARAM_DEPTH as u64,
                        },
                        allowed: MAX_AUTO_PARAM_DEPTH as u64,
                        observed: MAX_AUTO_PARAM_DEPTH as u64 + 1,
                    })
                    .with_progress("autoParam tactic evaluator depth"),
                ),
            )));
        }
        let saved = self.txn.lctx.clone();
        let depth = self.auto_param_depth;
        self.auto_param_depth += 1;
        let result = (|| {
            for parameter in parameters {
                self.tick()?;
                let declaration = self
                    .txn
                    .mvars
                    .get_decl(&parameter.id)
                    .cloned()
                    .ok_or_else(invalid)?;
                self.txn.lctx = declaration.lctx;
                let expected = self.instantiate(&declaration.type_)?;
                let proof = self.term(&parameter.tactic, Some(expected.clone()))?;
                self.constrain_type(&proof.type_, &expected)?;
                let value = self.instantiate(&proof.value)?;
                self.txn
                    .assign_mvar(parameter.id, value, AssignmentJustification::SyntheticHole)
                    .map_err(|error| {
                        failure(SourceInferenceError::Unification(Box::new(
                            UnificationError::Metavariable(error),
                        )))
                    })?;
            }
            Ok(())
        })();
        self.auto_param_depth = depth;
        self.txn.lctx = saved;
        result
    }

    fn quoted_whnf(&mut self, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        let locals = self.txn.lctx.clone();
        self.txn
            .whnf_with(value, &locals, budget)
            .map_err(|error| failure(SourceInferenceError::Unification(Box::new(error))))
    }

    fn quoted_constructor(
        &mut self,
        value: &Expr,
    ) -> Result<(Name, Vec<Expr>), NatDefinitionElabError> {
        let value = self.quoted_whnf(value)?;
        let mut head = &value;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(invalid());
        };
        if !matches!(self.txn.env.find(name), Some(ConstantInfo::Ctor(info))
            if !info.is_unsafe
                && info.num_params.checked_add(info.num_fields)
                    .and_then(|arity| usize::try_from(arity).ok()) == Some(arguments.len()))
        {
            return Err(invalid());
        }
        arguments.reverse();
        Ok((name.clone(), arguments))
    }

    fn quoted_string(&mut self, value: &Expr) -> Result<String, NatDefinitionElabError> {
        let value = self.quoted_whnf(value)?;
        match value.node() {
            ExprNode::Lit {
                literal: Literal::Str(value),
            } => {
                // One syntax atom can own an arbitrarily large literal. Pay
                // for its bytes before copying, in addition to tree-node work.
                for _ in value.as_bytes() {
                    self.tick()?;
                }
                Ok(value.clone())
            }
            _ => Err(invalid()),
        }
    }

    fn quoted_nat(&mut self, value: &Expr) -> Result<u64, NatDefinitionElabError> {
        let value = self.quoted_whnf(value)?;
        match value.node() {
            ExprNode::Lit {
                literal: Literal::Nat(value),
            } => value.to_u64().ok_or_else(invalid),
            _ => Err(invalid()),
        }
    }

    fn quoted_data_name(&mut self, mut value: Expr) -> Result<Name, NatDefinitionElabError> {
        enum Part {
            String(String),
            Number(u64),
        }
        let mut parts = Vec::new();
        loop {
            let (name, arguments) = self.quoted_constructor(&value)?;
            if name == Name::from_components(["Lean", "Name", "anonymous"]) && arguments.is_empty()
            {
                break;
            }
            let [prefix, part] = arguments.as_slice() else {
                return Err(invalid());
            };
            if name == Name::from_components(["Lean", "Name", "str"]) {
                parts.push(Part::String(self.quoted_string(part)?));
            } else if name == Name::from_components(["Lean", "Name", "num"]) {
                parts.push(Part::Number(self.quoted_nat(part)?));
            } else {
                return Err(invalid());
            }
            value = prefix.clone();
        }
        let mut name = Name::anonymous();
        for part in parts.into_iter().rev() {
            self.tick()?;
            name = match part {
                Part::String(part) => Name::str(name, part),
                Part::Number(part) => Name::num(name, part),
            };
        }
        Ok(name)
    }

    fn quoted_list(&mut self, mut value: Expr) -> Result<Vec<Expr>, NatDefinitionElabError> {
        let mut values = Vec::new();
        loop {
            let (name, arguments) = self.quoted_constructor(&value)?;
            if name == Name::from_components(["List", "nil"]) && arguments.len() == 1 {
                return Ok(values);
            }
            let [_, head, tail] = arguments.as_slice() else {
                return Err(invalid());
            };
            if name != Name::from_components(["List", "cons"]) {
                return Err(invalid());
            }
            values.push(head.clone());
            value = tail.clone();
        }
    }

    fn quoted_array(&mut self, value: &Expr) -> Result<Vec<Expr>, NatDefinitionElabError> {
        let (name, arguments) = self.quoted_constructor(value)?;
        let [_, list] = arguments.as_slice() else {
            return Err(invalid());
        };
        if name != Name::from_components(["Array", "mk"]) {
            return Err(invalid());
        }
        self.quoted_list(list.clone())
    }

    fn quoted_position(&mut self, value: &Expr) -> Result<BytePos, NatDefinitionElabError> {
        let (name, arguments) = self.quoted_constructor(value)?;
        let [index] = arguments.as_slice() else {
            return Err(invalid());
        };
        if name != Name::from_components(["String", "Pos", "Raw", "mk"]) {
            return Err(invalid());
        }
        usize::try_from(self.quoted_nat(index)?)
            .map(BytePos)
            .map_err(|_| invalid())
    }

    fn quoted_identifier(&mut self, value: &Expr) -> Result<RawIdentifier, NatDefinitionElabError> {
        let (name, arguments) = self.quoted_constructor(value)?;
        let [backing, start, stop] = arguments.as_slice() else {
            return Err(invalid());
        };
        if name != Name::from_components(["Substring", "Raw", "mk"]) {
            return Err(invalid());
        }
        let backing = self.quoted_string(backing)?;
        // Generated quotations use the entire backing. Its bytes have already
        // been charged by quoted_string. Certify that candidate range by
        // ordinary kernel conversion against the actual fields, avoiding a
        // full unifier normalization of the UTF-8 encoder for each identifier.
        // This is not a rule for a function name: changed definitions and real
        // substring slices must still establish their own values.
        let position = |index| {
            Expr::app(
                Expr::const_(
                    Name::from_components(["String", "Pos", "Raw", "mk"]),
                    Vec::new(),
                ),
                Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(index))),
            )
        };
        let length = u64::try_from(backing.len()).map_err(|_| invalid())?;
        let complete = self.coercion_kernel_eq(start.clone(), position(0))?
            && self.coercion_kernel_eq(stop.clone(), position(length))?;
        let (start, stop) = if complete {
            (BytePos(0), BytePos(backing.len()))
        } else {
            (self.quoted_position(start)?, self.quoted_position(stop)?)
        };
        let span = ByteSpan::new(start, stop).ok_or_else(invalid)?;
        RawIdentifier::owned(std::sync::Arc::from(backing), span).ok_or_else(invalid)
    }

    fn quoted_preresolved(
        &mut self,
        value: Expr,
    ) -> Result<Vec<Preresolved>, NatDefinitionElabError> {
        let mut values = Vec::new();
        for value in self.quoted_list(value)? {
            let (name, arguments) = self.quoted_constructor(&value)?;
            values.push(match arguments.as_slice() {
                [namespace]
                    if name
                        == Name::from_components([
                            "Lean",
                            "Syntax",
                            "Preresolved",
                            "namespace",
                        ]) =>
                {
                    Preresolved::Namespace {
                        ns: self.quoted_data_name(namespace.clone())?,
                    }
                }
                [declaration, fields]
                    if name == Name::from_components(["Lean", "Syntax", "Preresolved", "decl"]) =>
                {
                    let name = self.quoted_data_name(declaration.clone())?;
                    let mut names = Vec::new();
                    for field in self.quoted_list(fields.clone())? {
                        names.push(self.quoted_string(&field)?);
                    }
                    Preresolved::Decl {
                        name,
                        fields: names,
                    }
                }
                _ => return Err(invalid()),
            });
        }
        Ok(values)
    }

    fn quoted_info(&mut self, value: &Expr) -> Result<SourceInfo, NatDefinitionElabError> {
        // `quoteAutoTactic` erases every source position at the pin. Do not
        // reinterpret another file's positions against the caller's source.
        let (name, arguments) = self.quoted_constructor(value)?;
        if name == Name::from_components(["Lean", "SourceInfo", "none"]) && arguments.is_empty() {
            Ok(SourceInfo::None)
        } else {
            Err(invalid())
        }
    }

    fn auto_param_syntax(&mut self, value: Expr) -> Result<Syntax, NatDefinitionElabError> {
        enum Work {
            Visit(Expr),
            Finish(SourceInfo, Name, usize),
        }
        let mut work = vec![Work::Visit(value)];
        let mut built = Vec::new();
        while let Some(next) = work.pop() {
            self.tick()?;
            match next {
                Work::Finish(info, kind, start) => {
                    let args = built.split_off(start);
                    built.push(Syntax::Node { info, kind, args });
                }
                Work::Visit(value) => {
                    let (name, arguments) = self.quoted_constructor(&value)?;
                    match arguments.as_slice() {
                        [] if name == Name::from_components(["Lean", "Syntax", "missing"]) => {
                            built.push(Syntax::Missing);
                        }
                        [info, kind, children]
                            if name == Name::from_components(["Lean", "Syntax", "node"]) =>
                        {
                            let info = self.quoted_info(info)?;
                            let kind = self.quoted_data_name(kind.clone())?;
                            let children = self.quoted_array(children)?;
                            work.push(Work::Finish(info, kind, built.len()));
                            work.extend(children.into_iter().rev().map(Work::Visit));
                        }
                        [info, value]
                            if name == Name::from_components(["Lean", "Syntax", "atom"]) =>
                        {
                            built.push(Syntax::Atom {
                                info: self.quoted_info(info)?,
                                val: self.quoted_string(value)?,
                            });
                        }
                        [info, raw, value, preresolved]
                            if name == Name::from_components(["Lean", "Syntax", "ident"]) =>
                        {
                            built.push(Syntax::Ident {
                                info: self.quoted_info(info)?,
                                raw_val: self.quoted_identifier(raw)?,
                                val: self.quoted_data_name(value.clone())?,
                                preresolved: self.quoted_preresolved(preresolved.clone())?,
                            });
                        }
                        _ => return Err(invalid()),
                    }
                }
            }
        }
        if built.len() != 1 {
            return Err(invalid());
        }
        built.pop().ok_or_else(invalid)
    }
}
