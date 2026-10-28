//! What a definition by pattern matching leaves for its equation theorems, read off its source
//! when it is elaborated: the pin's matcher, as `elabMatchAltView` and `Match.mkMatcher` state it
//! (vendored `Lean/Elab/Match.lean`, `Lean/Meta/Match/Match.lean`).
//!
//! This engine compiles a `match` to recursor applications, which keep neither the alternatives
//! nor their right-hand sides apart. So once the definition is elaborated its root `match` is
//! elaborated a second time, in the definition's scope with the definition itself declared:
//! each alternative's patterns against the discriminants' types, its pattern variables as
//! locals, and its right-hand side against the motive at the patterns, recursive calls then
//! being applications of the constant, as the pin's equations state them. A match this does
//! not model is not recorded, and its equations are refused when asked for.
//!
//! Modelled: discriminants that are the definition's own parameters (section variables and
//! `fun x =>` binders included, a recursive call naming the definition with or without its
//! namespace), patterns that are variables, `_`, constructor applications (by name, `.c`,
//! `⟨…⟩`, a tuple), `Nat` literals and `n + k`, list literals and `::`, and `x@p`, over
//! inductive types without indices.
//!
//! The pin shares a matcher between matches of the same shape (`mkMatcherAuxDefinition` keys
//! its cache by the matcher's closed value, Match.lean:1087-1122), and the first one names the
//! fields and the motive's binders for all of them. The key here is that shape: the
//! discriminants' types and the patterns, closed over the parameters they use, with binder
//! names erased and universe parameters numbered. Only definitions' root matches are recorded,
//! so a matcher an earlier `theorem` or nested `match` created is not seen.
use super::super::*;
use super::journal::{self, Record};
use fln_env::constants::{ConstantInfo, DefinitionVal};

/// One elaborated alternative, over the opened parameters.
struct Alternative {
    fields: Vec<LocalDecl>,
    patterns: Vec<Expr>,
    rhs: Expr,
}

fn replace_fvar(expr: &Expr, id: &FVarId, value: &Expr) -> Option<Expr> {
    expr.abstract_fvar(id, 0)
        .ok()?
        .subst_loose(0, std::slice::from_ref(value))
        .ok()
}

fn hole_kind() -> Name {
    parser_kind(&["Term", "hole"])
}

fn is_kind(syntax: &Syntax, kind: &Name) -> bool {
    syntax.kind() == Some(kind)
}

fn node_args<'a>(syntax: &'a Syntax, kind: &Name) -> Option<&'a [Syntax]> {
    match syntax {
        Syntax::Node {
            kind: found, args, ..
        } if found == kind => Some(args),
        _ => None,
    }
}

fn null_args(syntax: &Syntax) -> Option<&[Syntax]> {
    node_args(syntax, &Name::from_components(["null"]))
}

/// The elements of a comma-separated `null` list.
fn separated(items: &[Syntax]) -> Option<Vec<&Syntax>> {
    let mut found = Vec::new();
    for (index, item) in items.iter().enumerate() {
        if index % 2 == 1 {
            if !matches!(item, Syntax::Atom { val, .. } if val == ",") {
                return None;
            }
        } else {
            found.push(item);
        }
    }
    Some(found)
}

/// The numeral a `num` node spells, when it is a decimal one.
fn numeral(syntax: &Syntax) -> Option<u64> {
    let args = node_args(syntax, &Name::from_components(["num"]))?;
    match args {
        [Syntax::Atom { val, .. }]
            if !val.is_empty() && val.bytes().all(|b| b.is_ascii_digit()) =>
        {
            val.parse().ok()
        }
        _ => None,
    }
}

fn nat_type() -> Expr {
    Expr::const_(Name::from_components(["Nat"]), Vec::new())
}

/// The variable name a pattern binder carries at the pin's matcher: its own, and `x` for a
/// `_` that is a whole pattern.
fn wildcard() -> Name {
    Name::from_components(["x"])
}

impl Context {
    /// The equation information of `definition`, whose value `body` elaborated, or `None` when
    /// its body is not a `match` this models. Its first `sections` parameters are the section
    /// variables it is closed over.
    pub(in crate::source) fn capture_equation_info(
        &self,
        definition: &DefinitionVal,
        body: &Syntax,
        sections: usize,
    ) -> Option<Record> {
        let (discriminants, alternatives) = match_parts(under_lambdas(body))?;
        // The definition is not admitted yet, and nothing here may admit it: its own name
        // is bound to a local while the alternatives elaborate (see `capture`).
        let mut scope = self.source_scope.clone();
        scope.variables = Default::default();
        let mut cx = Context::scoped(&self.txn.env, self.kernel, &scope);
        cx.txn.lctx = LocalContext::new();
        cx.level_params = definition.base.level_params.clone();
        cx.capture(definition, &discriminants, &alternatives, sections)
            .ok()
            .flatten()
    }

    fn capture(
        &mut self,
        definition: &DefinitionVal,
        discriminants: &[&Name],
        alternatives: &[(Vec<&Syntax>, &Syntax)],
        sections: usize,
    ) -> Result<Option<Record>, NatDefinitionElabError> {
        // The definition's value lambdas, opened with their binder names.
        let mut value = definition.value.clone();
        let mut type_ = definition.base.type_.clone();
        let mut parameters = Vec::new();
        // The type of the definition applied to its section variables.
        let mut applied = (sections == 0).then(|| type_.clone());
        while let ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = value.node()
        {
            self.tick()?;
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                binder_name.clone(),
                binder_type.clone(),
                *binder_info,
            );
            let local = Expr::fvar(id.clone());
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE { body: codomain, .. } = type_.node() else {
                return Ok(None);
            };
            type_ = self.substitute(codomain, &local)?;
            value = self.substitute(body, &local)?;
            parameters.push(id);
            if parameters.len() == sections {
                applied = Some(type_.clone());
            }
        }
        let result = type_;
        // The pin's `withFunLocalDecls` binds the definition's name to a local while its body
        // elaborates; inside a section, to the definition without the section variables it is
        // closed over. Its pre-definition then replaces that local by the constant applied to
        // them. A local of that application's type stands for it here, so a recursive
        // alternative elaborates without the definition entering any environment before the
        // kernel admits it.
        let Some(applied) = applied else {
            return Ok(None);
        };
        let levels = definition
            .base
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let value = parameters[..sections].iter().fold(
            Expr::const_(definition.base.name.clone(), levels),
            |head, id| Expr::app(head, Expr::fvar(id.clone())),
        );
        // The pin's auxiliary declaration answers to the full name too
        // (`auxDeclToFullName`, Lean/Elab/Term.lean).
        let mut names = Vec::new();
        if let LeafView::Str(short) = definition.base.name.leaf_view() {
            names.push(Name::from_components([short]));
        }
        if names.first() != Some(&definition.base.name) {
            names.push(definition.base.name.clone());
        }
        let mut recursion = Vec::new();
        for name in names {
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(id.clone(), name, applied.clone(), BinderInfo::Default);
            recursion.push(id);
        }
        let mut positions = Vec::new();
        for name in discriminants {
            let Some(position) = parameters.iter().rposition(|id| {
                self.txn
                    .lctx
                    .find(id)
                    .is_some_and(|local| &local.user_name == *name)
            }) else {
                return Ok(None);
            };
            if positions.contains(&position) {
                return Ok(None);
            }
            positions.push(position);
        }
        let opened = self.txn.lctx.len();
        let mut elaborated = Vec::new();
        for (patterns, rhs) in alternatives {
            if patterns.len() != positions.len() {
                return Ok(None);
            }
            let Some(alternative) =
                self.capture_alternative(&parameters, &positions, patterns, rhs, &result)?
            else {
                self.txn.lctx.truncate(opened);
                return Ok(None);
            };
            elaborated.push(alternative);
            self.txn.lctx.truncate(opened);
        }
        for alternative in &mut elaborated {
            for id in &recursion {
                let Some(rhs) = replace_fvar(&alternative.rhs, id, &value) else {
                    return Ok(None);
                };
                alternative.rhs = rhs;
            }
        }
        // Rebuild the alternatives' locals to close them.
        let mut closed = Vec::new();
        let mut field_names = Vec::new();
        let mut key_parts = Vec::new();
        for position in &positions {
            key_parts.push(
                self.txn
                    .lctx
                    .find(&parameters[*position])
                    .map(|local| local.type_.clone())
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?,
            );
        }
        for alternative in &elaborated {
            field_names.push(
                alternative
                    .fields
                    .iter()
                    .map(|local| local.user_name.clone())
                    .collect::<Vec<_>>(),
            );
        }
        for alternative in &elaborated {
            let body = pack(
                alternative
                    .patterns
                    .iter()
                    .cloned()
                    .chain([alternative.rhs.clone()]),
            );
            let fields = self.close_fields(&alternative.fields, body.clone())?;
            closed.push(self.close_parameters(&parameters, fields)?);
            let shape = self.close_fields(
                &alternative.fields,
                pack(alternative.patterns.iter().cloned()),
            )?;
            key_parts.push(shape);
        }
        let key = self.shape_key(&parameters, key_parts, &definition.base.level_params)?;
        // The motive's binders are the discriminants, the generated `x✝` of equations named `x`.
        let own_motive: Vec<Name> = positions
            .iter()
            .map(|position| {
                self.txn
                    .lctx
                    .find(&parameters[*position])
                    .map(|local| motive_name(&local.user_name))
                    .unwrap_or_else(wildcard)
            })
            .collect();
        let (motive_names, shared_fields) = match journal::read(&self.txn.env)?
            .into_iter()
            .find(|record| record.key == key)
        {
            Some(first) => {
                let mut names = Vec::new();
                for (alternative, own) in first.alternatives.iter().zip(&field_names) {
                    names.push(lambda_names(alternative, first.arity, own.len()));
                }
                (first.motive_names, Some(names))
            }
            None => (own_motive, None),
        };
        if let Some(shared) = &shared_fields {
            closed = closed
                .into_iter()
                .zip(shared)
                .map(|(alternative, names)| rename_lambdas(&alternative, parameters.len(), names))
                .collect();
        }
        Ok(Some(Record {
            declaration: definition.base.name.clone(),
            arity: parameters.len(),
            discriminants: positions,
            motive_names,
            key,
            alternatives: closed,
        }))
    }

    fn capture_alternative(
        &mut self,
        parameters: &[FVarId],
        positions: &[usize],
        patterns: &[&Syntax],
        rhs: &Syntax,
        result: &Expr,
    ) -> Result<Option<Alternative>, NatDefinitionElabError> {
        let mut builder = Builder::default();
        let mut elaborated: Vec<Expr> = Vec::new();
        for (column, syntax) in patterns.iter().enumerate() {
            let discriminant = &parameters[positions[column]];
            let mut expected = self
                .txn
                .lctx
                .find(discriminant)
                .map(|local| local.type_.clone())
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            for (earlier, pattern) in elaborated.iter().enumerate() {
                let Some(replaced) =
                    replace_fvar(&expected, &parameters[positions[earlier]], pattern)
                else {
                    return Ok(None);
                };
                expected = replaced;
            }
            let Some(pattern) = self.pattern(&mut builder, syntax, &expected, &wildcard())? else {
                return Ok(None);
            };
            elaborated.push(pattern);
        }
        let mut expected = result.clone();
        for (column, pattern) in elaborated.iter().enumerate() {
            let Some(replaced) = replace_fvar(&expected, &parameters[positions[column]], pattern)
            else {
                return Ok(None);
            };
            expected = replaced;
        }
        // `x@p`: the name is `p` in the right-hand side, as the pin's equations state it
        // (`Match.unfoldNamedPattern`).
        let mut lets = Vec::new();
        for (name, value) in &builder.named {
            let id = FVarId(self.fresh_name()?);
            let type_ = match self.known_type(value)? {
                Some(type_) => type_,
                None => return Ok(None),
            };
            self.txn
                .lctx
                .add_let(id.clone(), name.clone(), type_, value.clone());
            lets.push((id, value.clone()));
        }
        let Ok(term) = self.term(rhs, Some(expected)) else {
            return Ok(None);
        };
        let Ok(term) = self.finish(term) else {
            return Ok(None);
        };
        let mut rhs = term.value;
        for (id, value) in lets.iter().rev() {
            let Some(replaced) = replace_fvar(&rhs, id, value) else {
                return Ok(None);
            };
            rhs = replaced;
        }
        if rhs.has_expr_mvar() || rhs.has_level_mvar() {
            return Ok(None);
        }
        let mut patterns = Vec::new();
        for pattern in elaborated {
            let pattern = self.instantiate(&pattern)?;
            if pattern.has_expr_mvar() {
                return Ok(None);
            }
            patterns.push(pattern);
        }
        let mut fields = Vec::new();
        for field in &builder.fields {
            let mut local = self
                .txn
                .lctx
                .find(field)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            local.type_ = self.instantiate(&local.type_)?;
            if local.type_.has_expr_mvar() {
                return Ok(None);
            }
            fields.push(local);
        }
        Ok(Some(Alternative {
            fields,
            patterns,
            rhs,
        }))
    }

    /// A pattern against `expected`: its value, with its variables added as locals.
    fn pattern(
        &mut self,
        builder: &mut Builder,
        syntax: &Syntax,
        expected: &Expr,
        name: &Name,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.tick()?;
        let paren = parser_kind(&["Term", "paren"]);
        if let Some([_, inner, _]) = node_args(syntax, &paren) {
            return self.pattern(builder, inner, expected, name);
        }
        if is_kind(syntax, &hole_kind()) {
            return Ok(Some(builder.variable(
                self,
                name.clone(),
                expected.clone(),
            )?));
        }
        if let Some((alias, inner)) = super::super::patterns::named::parts(syntax)? {
            let Some(value) = self.pattern(builder, inner, expected, name)? else {
                return Ok(None);
            };
            builder.named.push((alias, value.clone()));
            return Ok(Some(value));
        }
        if let Syntax::Ident { val, .. } = syntax {
            if let Some(constructor) = self.pattern_constructor(val, expected)? {
                return self.constructor_pattern(builder, &constructor, &[], expected);
            }
            let erased = val.erase_macro_scopes();
            if erased.is_anonymous() || !erased.parent().is_anonymous() {
                return Ok(None);
            }
            return Ok(Some(builder.variable(
                self,
                val.clone(),
                expected.clone(),
            )?));
        }
        if numeral(syntax).is_some() {
            if !self.is_nat(expected)? {
                return Ok(None);
            }
            let Ok(term) = self.term(syntax, Some(expected.clone())) else {
                return Ok(None);
            };
            return Ok(Some(self.instantiate(&term.value)?));
        }
        if let Some([base, plus, offset]) = node_args(syntax, &Name::from_components(["term_+_"]))
            && matches!(plus, Syntax::Atom { val, .. } if val == "+")
            && let Some(offset) = numeral(offset)
        {
            if !self.is_nat(expected)? || offset > 4096 {
                return Ok(None);
            }
            let Some(mut value) = self.pattern(builder, base, expected, name)? else {
                return Ok(None);
            };
            for _ in 0..offset {
                self.tick()?;
                value = Expr::app(
                    Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new()),
                    value,
                );
            }
            return Ok(Some(value));
        }
        let app = parser_kind(&["Term", "app"]);
        if let Some([head, arguments]) = node_args(syntax, &app) {
            let Some(arguments) = null_args(arguments) else {
                return Ok(None);
            };
            let constructor = match head {
                Syntax::Ident { val, .. } => self.pattern_constructor(val, expected)?,
                _ if is_kind(head, &parser_kind(&["Term", "dotIdent"])) => {
                    self.dotted_constructor(head, expected)?
                }
                _ => None,
            };
            let Some(constructor) = constructor else {
                return Ok(None);
            };
            let arguments: Vec<&Syntax> = arguments.iter().collect();
            return self.constructor_pattern(builder, &constructor, &arguments, expected);
        }
        if is_kind(syntax, &parser_kind(&["Term", "dotIdent"])) {
            let Some(constructor) = self.dotted_constructor(syntax, expected)? else {
                return Ok(None);
            };
            return self.constructor_pattern(builder, &constructor, &[], expected);
        }
        if let Some([open, items, close]) =
            node_args(syntax, &parser_kind(&["Term", "anonymousCtor"]))
            && matches!(open, Syntax::Atom { val, .. } if val == "⟨")
            && matches!(close, Syntax::Atom { val, .. } if val == "⟩")
        {
            let Some(items) = null_args(items).and_then(separated) else {
                return Ok(None);
            };
            let Some(constructor) = self.structure_constructor(expected)? else {
                return Ok(None);
            };
            return self.constructor_pattern(builder, &constructor, &items, expected);
        }
        if let Some([_, items, _]) = node_args(syntax, &parser_kind(&["Term", "tuple"])) {
            let Some([first, comma, rest]) = null_args(items) else {
                return Ok(None);
            };
            if !matches!(comma, Syntax::Atom { val, .. } if val == ",") {
                return Ok(None);
            }
            let Some(rest) = null_args(rest).and_then(separated) else {
                return Ok(None);
            };
            if rest.len() != 1 {
                return Ok(None);
            }
            let Some(constructor) =
                self.pattern_constructor(&Name::from_components(["Prod", "mk"]), expected)?
            else {
                return Ok(None);
            };
            return self.constructor_pattern(builder, &constructor, &[first, rest[0]], expected);
        }
        if let Some([left, cons, right]) = node_args(syntax, &Name::from_components(["term_::_"]))
            && matches!(cons, Syntax::Atom { val, .. } if val == "::")
        {
            let Some(constructor) =
                self.pattern_constructor(&Name::from_components(["List", "cons"]), expected)?
            else {
                return Ok(None);
            };
            return self.constructor_pattern(builder, &constructor, &[left, right], expected);
        }
        if let Some([open, items, close]) = node_args(syntax, &Name::from_components(["term[_]"]))
            && matches!(open, Syntax::Atom { val, .. } if val == "[")
            && matches!(close, Syntax::Atom { val, .. } if val == "]")
        {
            let Some(items) = null_args(items).and_then(separated) else {
                return Ok(None);
            };
            return self.list_pattern(builder, &items, expected);
        }
        Ok(None)
    }

    fn list_pattern(
        &mut self,
        builder: &mut Builder,
        items: &[&Syntax],
        expected: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.tick()?;
        let Some((first, rest)) = items.split_first() else {
            let Some(nil) =
                self.pattern_constructor(&Name::from_components(["List", "nil"]), expected)?
            else {
                return Ok(None);
            };
            return self.constructor_pattern(builder, &nil, &[], expected);
        };
        let Some(cons) =
            self.pattern_constructor(&Name::from_components(["List", "cons"]), expected)?
        else {
            return Ok(None);
        };
        let Some((head_type, levels, params)) = self.constructor_instance(&cons, expected)? else {
            return Ok(None);
        };
        let _ = head_type;
        let Some(element) = params.first().cloned() else {
            return Ok(None);
        };
        let Some(head) =
            self.pattern(builder, first, &element, &Name::from_components(["head"]))?
        else {
            return Ok(None);
        };
        let Some(tail) = self.list_pattern(builder, rest, expected)? else {
            return Ok(None);
        };
        Ok(Some([element, head, tail].into_iter().fold(
            Expr::const_(cons.base.name.clone(), levels),
            Expr::app,
        )))
    }

    fn is_nat(&mut self, expected: &Expr) -> Result<bool, NatDefinitionElabError> {
        let type_ = self.whnf(expected)?;
        Ok(type_ == nat_type())
    }

    /// The inductive type `expected` is, with its levels and parameters, when it has no indices.
    fn inductive_instance(
        &mut self,
        expected: &Expr,
    ) -> Result<Option<Instance<fln_env::constants::InductiveVal>>, NatDefinitionElabError> {
        let type_ = self.whnf(expected)?;
        let mut args = Vec::new();
        let mut head = &type_;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            head = f;
        }
        args.reverse();
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(inductive)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if inductive.num_indices != 0 || args.len() != inductive.num_params as usize {
            return Ok(None);
        }
        Ok(Some((inductive, levels.clone(), args)))
    }

    fn constructor_instance(
        &mut self,
        constructor: &fln_env::constants::ConstructorVal,
        expected: &Expr,
    ) -> Result<Option<Instance<Expr>>, NatDefinitionElabError> {
        let Some((inductive, levels, params)) = self.inductive_instance(expected)? else {
            return Ok(None);
        };
        if constructor.induct != inductive.base.name {
            return Ok(None);
        }
        let type_ = self.instantiate_params(
            &constructor.base.type_,
            &constructor.base.level_params,
            &levels,
        )?;
        Ok(Some((type_, levels, params)))
    }

    /// The constructor `name` resolves to, when it is one of `expected`'s.
    fn pattern_constructor(
        &mut self,
        name: &Name,
        expected: &Expr,
    ) -> Result<Option<fln_env::constants::ConstructorVal>, NatDefinitionElabError> {
        let resolved = match self.resolve_source_name(name) {
            Ok(Some(resolved)) => resolved,
            // `true` and `false` are `Bool`'s, as a term reads them (`Context::atom`).
            _ if *name == Name::from_components(["true"]) => {
                Name::from_components(["Bool", "true"])
            }
            _ if *name == Name::from_components(["false"]) => {
                Name::from_components(["Bool", "false"])
            }
            _ => return Ok(None),
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&resolved).cloned() else {
            return Ok(None);
        };
        Ok(self
            .inductive_instance(expected)?
            .filter(|(inductive, _, _)| inductive.base.name == constructor.induct)
            .map(|_| constructor))
    }

    fn dotted_constructor(
        &mut self,
        syntax: &Syntax,
        expected: &Expr,
    ) -> Result<Option<fln_env::constants::ConstructorVal>, NatDefinitionElabError> {
        let Some([_, Syntax::Ident { val, .. }]) =
            node_args(syntax, &parser_kind(&["Term", "dotIdent"]))
        else {
            return Ok(None);
        };
        let Some((inductive, _, _)) = self.inductive_instance(expected)? else {
            return Ok(None);
        };
        let name = inductive.base.name.append_core(val);
        match self.txn.env.find(&name).cloned() {
            Some(ConstantInfo::Ctor(constructor)) => Ok(Some(constructor)),
            _ => Ok(None),
        }
    }

    fn structure_constructor(
        &mut self,
        expected: &Expr,
    ) -> Result<Option<fln_env::constants::ConstructorVal>, NatDefinitionElabError> {
        let Some((inductive, _, _)) = self.inductive_instance(expected)? else {
            return Ok(None);
        };
        let [constructor] = inductive.ctors.as_slice() else {
            return Ok(None);
        };
        match self.txn.env.find(constructor).cloned() {
            Some(ConstantInfo::Ctor(constructor)) => Ok(Some(constructor)),
            _ => Ok(None),
        }
    }

    /// `C a₁ … aₙ` against `expected`: the parameters from the type, a written argument for
    /// each explicit field and a variable for each other.
    fn constructor_pattern(
        &mut self,
        builder: &mut Builder,
        constructor: &fln_env::constants::ConstructorVal,
        arguments: &[&Syntax],
        expected: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some((mut type_, levels, params)) = self.constructor_instance(constructor, expected)?
        else {
            return Ok(None);
        };
        let mut value = Expr::const_(constructor.base.name.clone(), levels);
        for param in &params {
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Ok(None);
            };
            type_ = self.substitute(body, param)?;
            value = Expr::app(value, param.clone());
        }
        let mut remaining = arguments.iter();
        for _ in 0..constructor.num_fields {
            self.tick()?;
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = type_.node()
            else {
                return Ok(None);
            };
            let (binder_name, binder_type, body) =
                (binder_name.clone(), binder_type.clone(), body.clone());
            let field = if *binder_info == BinderInfo::Default {
                let Some(argument) = remaining.next() else {
                    return Ok(None);
                };
                match self.pattern(builder, argument, &binder_type, &binder_name)? {
                    Some(field) => field,
                    None => return Ok(None),
                }
            } else {
                builder.variable(self, binder_name, binder_type)?
            };
            type_ = self.substitute(&body, &field)?;
            value = Expr::app(value, field);
        }
        if remaining.next().is_some() {
            return Ok(None);
        }
        Ok(Some(value))
    }

    fn close_fields(
        &mut self,
        fields: &[LocalDecl],
        body: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut body = body;
        for local in fields.iter().rev() {
            self.tick()?;
            body = Expr::lam(
                local.user_name.clone(),
                local.type_.clone(),
                body.abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
        }
        Ok(body)
    }

    fn close_parameters(
        &mut self,
        parameters: &[FVarId],
        body: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut body = body;
        for id in parameters.iter().rev() {
            self.tick()?;
            let local = self
                .txn
                .lctx
                .find(id)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            body = Expr::lam(
                local.user_name,
                local.type_,
                body.abstract_fvar(id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        if body.has_fvar() || body.has_loose_bvars() {
            return Err(failure(SourceInferenceError::Scope));
        }
        Ok(body)
    }

    /// The matcher's cache key, up to what `Expr.eqv` ignores: the parts closed over the
    /// parameters they mention, binder names erased, universe parameters by first use.
    fn shape_key(
        &mut self,
        parameters: &[FVarId],
        parts: Vec<Expr>,
        level_params: &[Name],
    ) -> Result<Expr, NatDefinitionElabError> {
        let body = pack(parts);
        let used: Vec<FVarId> = parameters
            .iter()
            .filter(|id| mentions(&body, id))
            .cloned()
            .collect();
        let mut closed = body;
        for id in used.iter().rev() {
            let local = self
                .txn
                .lctx
                .find(id)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            closed = Expr::lam(
                Name::anonymous(),
                local.type_,
                closed
                    .abstract_fvar(id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
        }
        if closed.has_fvar() {
            // A parameter's type mentions an unused parameter: close over every parameter.
            return Err(failure(SourceInferenceError::Scope));
        }
        Ok(erase_names(&closed, level_params))
    }
}

#[derive(Default)]
struct Builder {
    fields: Vec<FVarId>,
    named: Vec<(Name, Expr)>,
}

impl Builder {
    fn variable(
        &mut self,
        cx: &mut Context,
        name: Name,
        type_: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let id = FVarId(cx.fresh_name()?);
        cx.txn
            .lctx
            .add_param(id.clone(), name, type_, BinderInfo::Default);
        self.fields.push(id.clone());
        Ok(Expr::fvar(id))
    }
}

fn pack(args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter()
        .fold(Expr::const_(journal::pack_name(), Vec::new()), Expr::app)
}

fn motive_name(name: &Name) -> Name {
    let erased = name.erase_macro_scopes();
    let text = erased.to_display_string();
    if erased.is_anonymous()
        || !erased.parent().is_anonymous()
        || matches!(erased.leaf_view(), LeafView::Num(_))
        || text.starts_with("_fln")
    {
        wildcard()
    } else {
        erased
    }
}

fn mentions(expr: &Expr, id: &FVarId) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if !expr.has_fvar() {
            continue;
        }
        match expr.node() {
            ExprNode::FVar { id: found } if found == id => return true,
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

/// Binder names erased, metadata dropped, universe parameters renamed by first use.
fn erase_names(expr: &Expr, level_params: &[Name]) -> Expr {
    let mut order: Vec<Name> = Vec::new();
    fn level(source: &Level, order: &mut Vec<Name>, params: &[Name]) -> Level {
        use fln_core::level::LevelView;
        match source.view() {
            LevelView::Zero => Level::zero(),
            LevelView::Succ(inner) => level(inner, order, params)
                .succ()
                .unwrap_or_else(|_| inner.clone()),
            LevelView::Max(a, b) => {
                let (a, b) = (level(a, order, params), level(b, order, params));
                Level::max(a.clone(), b).unwrap_or(a)
            }
            LevelView::IMax(a, b) => {
                let (a, b) = (level(a, order, params), level(b, order, params));
                Level::imax(a.clone(), b).unwrap_or(a)
            }
            LevelView::Param(name) if params.contains(name) => {
                let index = order
                    .iter()
                    .position(|seen| seen == name)
                    .unwrap_or_else(|| {
                        order.push(name.clone());
                        order.len() - 1
                    });
                Level::param(Name::num(Name::from_components(["_fln_key"]), index as u64))
            }
            _ => source.clone(),
        }
    }
    fn go(expr: &Expr, order: &mut Vec<Name>, params: &[Name]) -> Expr {
        match expr.node() {
            ExprNode::Sort { level: l } => Expr::sort(level(l, order, params)),
            ExprNode::Const { name, levels } => Expr::const_(
                name.clone(),
                levels.iter().map(|l| level(l, order, params)).collect(),
            ),
            ExprNode::App { f, a } => Expr::app(go(f, order, params), go(a, order, params)),
            ExprNode::Lam {
                binder_type,
                body,
                binder_info,
                ..
            } => Expr::lam(
                Name::anonymous(),
                go(binder_type, order, params),
                go(body, order, params),
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } => Expr::forall_e(
                Name::anonymous(),
                go(binder_type, order, params),
                go(body, order, params),
                *binder_info,
            ),
            ExprNode::LetE {
                type_,
                value,
                body,
                non_dep,
                ..
            } => Expr::let_e(
                Name::anonymous(),
                go(type_, order, params),
                go(value, order, params),
                go(body, order, params),
                *non_dep,
            ),
            ExprNode::MData { expr, .. } => go(expr, order, params),
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(struct_name.clone(), *idx, go(expr, order, params)),
            _ => expr.clone(),
        }
    }
    go(expr, &mut order, level_params)
}

/// The names of the `count` lambdas after the first `skip` of `expr`.
fn lambda_names(expr: &Expr, skip: usize, count: usize) -> Vec<Name> {
    let mut names = Vec::new();
    let mut current = expr;
    let mut seen = 0;
    while let ExprNode::Lam {
        binder_name, body, ..
    } = current.node()
    {
        if seen >= skip && names.len() < count {
            names.push(binder_name.clone());
        }
        seen += 1;
        current = body;
    }
    names
}

/// `expr` with the lambdas after the first `skip` renamed to `names`.
fn rename_lambdas(expr: &Expr, skip: usize, names: &[Name]) -> Expr {
    fn go(expr: &Expr, skip: usize, names: &[Name], index: usize) -> Expr {
        match expr.node() {
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } if index < skip + names.len() => {
                let name = if index >= skip {
                    names[index - skip].clone()
                } else {
                    binder_name.clone()
                };
                Expr::lam(
                    name,
                    binder_type.clone(),
                    go(body, skip, names, index + 1),
                    *binder_info,
                )
            }
            _ => expr.clone(),
        }
    }
    go(expr, skip, names, 0)
}

/// A written `match` alternative: its patterns and right-hand side.
type WrittenAlternative<'a> = (Vec<&'a Syntax>, &'a Syntax);

/// An inductive type, or a constructor's type, at the levels and parameters of an instance.
type Instance<T> = (T, Vec<Level>, Vec<Expr>);

/// `body` under `fun x y =>` binders that are plain identifiers: the definition's value
/// lambdas, which [`Context::capture`] opens with the parameters.
fn under_lambdas(mut body: &Syntax) -> &Syntax {
    while let Some([keyword, basic]) = node_args(body, &parser_kind(&["Term", "fun"])) {
        let Some([binders, type_, arrow, inner]) =
            node_args(basic, &parser_kind(&["Term", "basicFun"]))
        else {
            break;
        };
        let plain = null_args(binders)
            .is_some_and(|binders| binders.iter().all(|b| matches!(b, Syntax::Ident { .. })));
        if !matches!(keyword, Syntax::Atom { val, .. } if val == "fun")
            || !matches!(arrow, Syntax::Atom { val, .. } if val == "=>")
            || !null_args(type_).is_some_and(<[Syntax]>::is_empty)
            || !plain
        {
            break;
        }
        body = inner;
    }
    body
}

/// The discriminant identifiers and alternatives (patterns, right-hand side) of a `match`
/// with no motive, generalization or `h :` annotations.
fn match_parts(body: &Syntax) -> Option<(Vec<&Name>, Vec<WrittenAlternative<'_>>)> {
    let args = node_args(body, &parser_kind(&["Term", "match"]))?;
    let [
        keyword,
        generalizing,
        motive,
        discriminants,
        with,
        alternatives,
    ] = args
    else {
        return None;
    };
    if !matches!(keyword, Syntax::Atom { val, .. } if val == "match")
        || !matches!(with, Syntax::Atom { val, .. } if val == "with")
        || !null_args(generalizing)?.is_empty()
        || !null_args(motive)?.is_empty()
    {
        return None;
    }
    let mut names = Vec::new();
    for discriminant in separated(null_args(discriminants)?)? {
        let [binder, term] = node_args(discriminant, &parser_kind(&["Term", "matchDiscr"]))? else {
            return None;
        };
        if !null_args(binder)?.is_empty() {
            return None;
        }
        let Syntax::Ident { val, .. } = term else {
            return None;
        };
        names.push(val);
    }
    let [rows] = node_args(alternatives, &parser_kind(&["Term", "matchAlts"]))? else {
        return None;
    };
    let mut alternatives = Vec::new();
    for row in null_args(rows)? {
        let [bar, patterns, arrow, rhs] = node_args(row, &parser_kind(&["Term", "matchAlt"]))?
        else {
            return None;
        };
        if !matches!(bar, Syntax::Atom { val, .. } if val == "|")
            || !matches!(arrow, Syntax::Atom { val, .. } if val == "=>")
        {
            return None;
        }
        let [patterns] = null_args(patterns)? else {
            return None;
        };
        alternatives.push((separated(null_args(patterns)?)?, rhs));
    }
    (!names.is_empty() && !alternatives.is_empty()).then_some((names, alternatives))
}
