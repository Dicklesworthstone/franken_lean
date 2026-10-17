//! Heap-driven, binder-aware normalization. Cache keys include the opened
//! telescope; retained input Arcs prevent pointer reuse from aliasing a key.
use super::*;

const MAX_NODES: usize = 100_000;
type Key = (usize, usize);

enum Frame {
    Visit(Expr, usize),
    Cache(Expr, Key),
    App(Expr, Key),
    Proj(Expr, Key),
    Domain(Expr, Key),
    Body { original: Expr, key: Key, local: LocalDecl, outer: LocalContext },
}

impl Context {
    pub(super) fn dsimp_expression(
        &mut self,
        expr: &Expr,
        rules: &Rules<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let original_context = trial.txn.lctx.clone();
        let result = trial.dsimp_walk(expr, rules);
        trial.txn.lctx = original_context;
        self.charge_rewrite_trial(&trial);
        if result.is_ok() { *self = trial; }
        result
    }

    fn dsimp_walk(&mut self, expr: &Expr, rules: &Rules<'_>) -> Result<Expr, NatDefinitionElabError> {
        let mut work = vec![Frame::Visit(expr.clone(), 0)];
        let mut values: Vec<Expr> = Vec::new();
        let mut cache: HashMap<Key, (Expr, Expr)> = HashMap::new();
        let mut scope = 0usize;
        let mut visited = 0usize;
        while let Some(frame) = work.pop() {
            self.tick()?;
            match frame {
                Frame::Visit(expr, context) => {
                    let key = (expr.allocation_identity(), context);
                    if let Some((_, value)) = cache.get(&key) {
                        values.push(value.clone());
                        continue;
                    }
                    visited += 1;
                    if visited > MAX_NODES { return Err(failure(SourceInferenceError::ResourceLimit)); }
                    if let Some(type_) = self.known_type(&expr)?
                        && self.dsimp_is_proposition(&type_)?
                    {
                        cache.insert(key, (expr.clone(), expr.clone()));
                        values.push(expr);
                        continue;
                    }
                    if self.dsimp_literal(&expr, rules)? {
                        let next = self.dsimp_rewrite_head(&expr, rules)?;
                        if self.rewrite_same(&next, &expr)? {
                            cache.insert(key, (expr.clone(), expr.clone()));
                            values.push(expr);
                        } else {
                            work.push(Frame::Cache(expr, key));
                            work.push(Frame::Visit(next, context));
                        }
                        continue;
                    }
                    // Reducing the head first also avoids traversing dead let
                    // values. The post-child pass below revisits newly exposed
                    // beta/iota/projection and selected-definition redexes.
                    let next = self.dsimp_head(&expr, rules)?;
                    if !self.rewrite_same(&next, &expr)? {
                        work.push(Frame::Cache(expr, key));
                        work.push(Frame::Visit(next, context));
                        continue;
                    }
                    match expr.node() {
                        ExprNode::App { f, a } => {
                            let (f, a) = (f.clone(), a.clone());
                            work.push(Frame::App(expr, key));
                            work.push(Frame::Visit(a, context));
                            work.push(Frame::Visit(f, context));
                        }
                        ExprNode::Lam { binder_type, .. } | ExprNode::ForallE { binder_type, .. } => {
                            let domain = binder_type.clone();
                            work.push(Frame::Domain(expr, key));
                            work.push(Frame::Visit(domain, context));
                        }
                        ExprNode::Proj { expr: receiver, .. } => {
                            let receiver = receiver.clone();
                            work.push(Frame::Proj(expr, key));
                            work.push(Frame::Visit(receiver, context));
                        }
                        _ => {
                            cache.insert(key, (expr.clone(), expr.clone()));
                            values.push(expr);
                        }
                    }
                }
                Frame::Cache(original, key) => {
                    let result = values.last().expect("visited dsimp result").clone();
                    cache.insert(key, (original, result));
                }
                Frame::Domain(original, key) => {
                    let domain = values.pop().expect("dsimp binder domain");
                    let (body, info) = match original.node() {
                        ExprNode::Lam { body, binder_info, .. }
                        | ExprNode::ForallE { body, binder_info, .. } => (body, *binder_info),
                        _ => unreachable!("binder frame"),
                    };
                    let mut local = self.equality_local(domain)?;
                    local.binder_info = info;
                    let opened = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                    let outer = self.txn.lctx.clone();
                    eliminate::add_local(&mut self.txn.lctx, &local);
                    scope = scope.checked_add(1).ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                    work.push(Frame::Body { original, key, local, outer });
                    work.push(Frame::Visit(opened, scope));
                }
                Frame::Body { original, key, mut local, outer } => {
                    let body = values.pop().expect("dsimp binder body");
                    let (name, lambda) = match original.node() {
                        ExprNode::Lam { binder_name, .. } => (binder_name.clone(), true),
                        ExprNode::ForallE { binder_name, .. } => (binder_name.clone(), false),
                        _ => unreachable!("binder frame"),
                    };
                    // Keep fresh internal names while visiting the body so an
                    // explicit rule cannot be captured by its binder spelling.
                    local.user_name = name;
                    let result = self.close_equality_binder(&local, body, lambda)?;
                    self.txn.lctx = outer;
                    let next = self.dsimp_head(&result, rules)?;
                    work.push(Frame::Cache(original, key));
                    if self.rewrite_same(&result, &next)? { values.push(result); }
                    else { work.push(Frame::Visit(next, key.1)); }
                }
                Frame::App(original, key) => {
                    let a = values.pop().expect("dsimp argument");
                    let f = values.pop().expect("dsimp function");
                    let result = Expr::app(f, a);
                    let next = self.dsimp_head(&result, rules)?;
                    work.push(Frame::Cache(original, key));
                    if self.rewrite_same(&result, &next)? { values.push(result); }
                    else { work.push(Frame::Visit(next, key.1)); }
                }
                Frame::Proj(original, key) => {
                    let receiver = values.pop().expect("dsimp projection receiver");
                    let ExprNode::Proj { struct_name, idx, .. } = original.node() else { unreachable!("projection frame"); };
                    let result = Expr::proj(struct_name.clone(), *idx, receiver);
                    let next = self.dsimp_head(&result, rules)?;
                    work.push(Frame::Cache(original, key));
                    if self.rewrite_same(&result, &next)? { values.push(result); }
                    else { work.push(Frame::Visit(next, key.1)); }
                }
            }
        }
        let result = values.pop().expect("dsimp root result");
        assert!(values.is_empty(), "one dsimp result");
        Ok(result)
    }

    fn dsimp_literal(&mut self, expr: &Expr, rules: &Rules<'_>) -> Result<bool, NatDefinitionElabError> {
        let (head, args) = self.dsimp_spine(expr)?;
        let ExprNode::Const { name, .. } = head.node() else { return Ok(false); };
        if rules.definitions.contains_key(name) { return Ok(false); }
        let nat = |expr: &Expr| matches!(expr.node(), ExprNode::Lit { literal: Literal::Nat(_) });
        Ok((name == &Name::from_components(["OfNat", "ofNat"]) && args.len() >= 3 && nat(&args[1]))
            || (name == &Name::from_components(["OfScientific", "ofScientific"])
                && args.len() == 5 && nat(&args[2]) && nat(&args[4]))
            || (name == &Name::from_components(["Char", "ofNat"]) && args.len() == 1 && nat(&args[0])))
    }

    fn dsimp_spine(&mut self, expr: &Expr) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = expr.clone();
        let mut args = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            args.push(a.clone());
            head = f.clone();
        }
        args.reverse();
        Ok((head, args))
    }

    fn dsimp_head(&mut self, expr: &Expr, rules: &Rules<'_>) -> Result<Expr, NatDefinitionElabError> {
        let reduced = self.whnf_with_transparency(expr, UnificationTransparency::None, false)?;
        if !self.rewrite_same(expr, &reduced)? { return Ok(reduced); }
        if let ExprNode::FVar { id } = expr.node()
            && let Some(value) = rules.lets.get(id)
        { return Ok(value.clone()); }
        let (head, args) = self.dsimp_spine(expr)?;
        if let ExprNode::Const { name, .. } = head.node() {
            if let Some(definition) = rules.definitions.get(name)
                && self.dsimp_unfoldable(definition)?
            {
                let mut arity = 0;
                let mut body = &definition.value;
                while let ExprNode::Lam { body: rest, .. } = body.node() {
                    self.tick()?; arity += 1; body = rest;
                }
                if args.len() >= arity {
                    let unfolded = self.unfold_selected_definition(expr, definition)?;
                    if !self.rewrite_same(expr, &unfolded)? { return Ok(unfolded); }
                }
            }
            if let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned()
                && self.dsimp_unfoldable(&definition)?
                && let Some(projected) = self.dsimp_projection(&definition, &head, &args)?
            { return Ok(projected); }
        }
        self.dsimp_rewrite_head(expr, rules)
    }

    fn dsimp_unfoldable(&mut self, definition: &DefinitionVal) -> Result<bool, NatDefinitionElabError> {
        self.tick()?;
        let table = crate::reducibility::table(&self.txn.env).map_err(|e|
            failure(SourceInferenceError::Unification(Box::new(UnificationError::Reducibility(e)))))?;
        Ok(definition.safety == DefinitionSafety::Safe
            && table.status(&definition.base.name) != crate::reducibility::Reducibility::Irreducible)
    }

    // Only an admitted, generated field of a single-constructor record receives
    // automatic projection behavior. A function with a similar suffix/body does
    // not. Stuck receivers and unapplied projections retain their original form.
    fn dsimp_projection(
        &mut self,
        definition: &DefinitionVal,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut body = &definition.value;
        let mut binders = 0usize;
        while let ExprNode::Lam { body: rest, .. } = body.node() {
            self.tick()?; binders += 1; body = rest;
        }
        let ExprNode::Proj { struct_name, idx, expr } = body.node() else { return Ok(None); };
        if !matches!(expr.node(), ExprNode::BVar { idx: 0 }) { return Ok(None); }
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(struct_name).cloned() else { return Ok(None); };
        let parameters = family.num_params as usize;
        if family.is_unsafe || family.num_indices != 0 || family.ctors.len() != 1
            || binders != parameters + 1 || args.len() < binders { return Ok(None); }
        let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(&family.ctors[0]).cloned() else { return Ok(None); };
        if ctor.is_unsafe || ctor.induct != *struct_name || *idx >= u64::from(ctor.num_fields) { return Ok(None); }
        let mut field = &ctor.base.type_;
        for _ in 0..u64::from(family.num_params) + idx {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = field.node() else { return Ok(None); };
            field = body;
        }
        let ExprNode::ForallE { binder_name, .. } = field.node() else { return Ok(None); };
        if definition.base.name != struct_name.append_core(binder_name) { return Ok(None); }
        let receiver = self.whnf_with_transparency(&args[parameters], UnificationTransparency::Abbreviations, true)?;
        let (receiver_head, _) = self.dsimp_spine(&receiver)?;
        if !matches!(receiver_head.node(), ExprNode::Const { name, .. } if name == &ctor.base.name) { return Ok(None); }
        let mut applied = args.to_vec();
        applied[parameters] = receiver;
        let application = app(head.clone(), applied);
        let unfolded = self.unfold_selected_definition(&application, definition)?;
        Ok(Some(self.whnf_with_transparency(&unfolded, UnificationTransparency::None, false)?))
    }
}
