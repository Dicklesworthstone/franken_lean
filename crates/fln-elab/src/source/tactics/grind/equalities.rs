//! Bounded congruence closure with ordinary equality proofs on every edge.
use super::*;

const MAX_TERMS: usize = 512;

#[derive(Clone)]
pub(super) struct Node {
    pub term: Expr,
    pub type_: Expr,
    pub level: Level,
    pub application: Option<(usize, usize)>,
    pub proposition: bool,
}

#[derive(Clone, Default)]
pub(super) struct Equalities {
    pub nodes: Vec<Node>,
    indices: HashMap<Expr, usize>,
    parents: Vec<usize>,
    edges: Vec<Vec<(usize, Expr)>>,
    pub consequences: Vec<Typed>,
}

impl Equalities {
    pub fn intern(&mut self, context: &mut Context, expression: &Expr) -> Result<usize, Error> {
        let expression = normalize(context, expression)?;
        let mut pending = vec![(expression.clone(), false)];
        while let Some((term, ready)) = pending.pop() {
            context.tick()?;
            let term = normalize(context, &term)?;
            if self.indices.contains_key(&term) {
                continue;
            }
            if self.nodes.len() >= MAX_TERMS || pending.len() > MAX_TERMS * 3 {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            if !ready && let ExprNode::App { f, a } = term.node() {
                pending.push((term.clone(), true));
                pending.push((a.clone(), false));
                pending.push((f.clone(), false));
                continue;
            }
            let type_ = context.known_type(&term)?.ok_or_else(unsupported)?;
            let sort = context.known_type(&type_)?.ok_or_else(unsupported)?;
            let level = context.sort_level(&Typed {
                value: type_.clone(),
                type_: sort,
            })?;
            let proposition = is_prop(context, &term)?;
            let application = if let ExprNode::App { f, a } = term.node() {
                Some((
                    self.indices[&normalize(context, f)?],
                    self.indices[&normalize(context, a)?],
                ))
            } else {
                None
            };
            let id = self.nodes.len();
            self.indices.insert(term.clone(), id);
            self.nodes.push(Node {
                term,
                type_,
                level,
                application,
                proposition,
            });
            self.parents.push(id);
            self.edges.push(Vec::new());
        }
        Ok(self.indices[&expression])
    }

    fn root(&self, mut id: usize) -> usize {
        while self.parents[id] != id {
            id = self.parents[id];
        }
        id
    }

    fn join(
        &mut self,
        context: &mut Context,
        left: usize,
        right: usize,
        proof: Expr,
    ) -> Result<bool, Error> {
        let a = self.root(left);
        let b = self.root(right);
        if a == b {
            return Ok(false);
        }
        context.tick()?;
        if !convert(context, &self.nodes[left].type_, &self.nodes[right].type_)? {
            return Ok(false);
        }
        let node = &self.nodes[left];
        let symmetric = context.symmetric_equality(
            &node.level,
            &node.type_,
            &node.term,
            &self.nodes[right].term,
            proof.clone(),
        )?;
        self.consequences.push(Typed {
            value: proof.clone(),
            type_: equality::equation(
                node.level.clone(),
                node.type_.clone(),
                node.term.clone(),
                self.nodes[right].term.clone(),
            ),
        });
        self.edges[left].push((right, proof));
        self.edges[right].push((left, symmetric));
        self.parents[a.max(b)] = a.min(b);
        Ok(true)
    }

    pub fn add(&mut self, context: &mut Context, evidence: &Typed) -> Result<(), Error> {
        let type_ = normalize(context, &evidence.type_)?;
        let Some((_, _, left, right)) = equality_target(&type_) else {
            return Ok(());
        };
        let left = self.intern(context, &left)?;
        let right = self.intern(context, &right)?;
        self.join(context, left, right, evidence.value.clone())?;
        Ok(())
    }

    fn explain(
        &self,
        context: &mut Context,
        left: usize,
        right: usize,
    ) -> Result<Option<Expr>, Error> {
        if self.root(left) != self.root(right) {
            return Ok(None);
        }
        let node = &self.nodes[left];
        if left == right {
            return Ok(Some(equality::reflexivity(
                node.level.clone(),
                node.type_.clone(),
                node.term.clone(),
            )));
        }
        let mut previous: Vec<Option<(usize, Expr)>> = vec![None; self.nodes.len()];
        let mut queue = VecDeque::from([left]);
        let mut seen = vec![false; self.nodes.len()];
        seen[left] = true;
        while let Some(at) = queue.pop_front() {
            context.tick()?;
            if at == right {
                break;
            }
            for (next, proof) in &self.edges[at] {
                context.tick()?;
                if !seen[*next] {
                    seen[*next] = true;
                    previous[*next] = Some((at, proof.clone()));
                    queue.push_back(*next);
                }
            }
        }
        let mut path = Vec::new();
        let mut at = right;
        while at != left {
            context.tick()?;
            let (from, proof) = previous[at].clone().ok_or_else(unsupported)?;
            path.push((from, at, proof));
            at = from;
        }
        let mut proof =
            equality::reflexivity(node.level.clone(), node.type_.clone(), node.term.clone());
        for (from, to, edge) in path.into_iter().rev() {
            context.tick()?;
            proof = self.trans(left, from, to, proof, edge);
        }
        Ok(Some(proof))
    }

    fn trans(&self, left: usize, middle: usize, right: usize, first: Expr, second: Expr) -> Expr {
        let node = &self.nodes[left];
        apply(
            Expr::const_(name("Eq.trans"), vec![node.level.clone()]),
            [
                node.type_.clone(),
                node.term.clone(),
                self.nodes[middle].term.clone(),
                self.nodes[right].term.clone(),
                first,
                second,
            ],
        )
    }

    pub fn equation(
        &mut self,
        context: &mut Context,
        left: &Expr,
        right: &Expr,
    ) -> Result<Option<Expr>, Error> {
        let left = self.intern(context, left)?;
        let right = self.intern(context, right)?;
        self.explain(context, left, right)
    }

    // The pin does not enable congruence on arbitrary named partial functions
    // without funCC metadata. Local functions, and the same constant with equal
    // complete prefixes, are safe here. Equality of two opaque partial
    // applications alone is deliberately insufficient.
    fn function_congruence(
        &self,
        context: &mut Context,
        mut left: usize,
        mut right: usize,
    ) -> Result<bool, Error> {
        if left == right {
            return Ok(true);
        }
        let mut left_args = Vec::new();
        let mut right_args = Vec::new();
        while let Some((head, argument)) = self.nodes[left].application {
            context.tick()?;
            left_args.push(argument);
            left = head;
        }
        while let Some((head, argument)) = self.nodes[right].application {
            context.tick()?;
            right_args.push(argument);
            right = head;
        }
        Ok(
            match (self.nodes[left].term.node(), self.nodes[right].term.node()) {
                (ExprNode::FVar { .. }, ExprNode::FVar { .. }) => true,
                (
                    ExprNode::Const { name: f, levels: u },
                    ExprNode::Const { name: g, levels: v },
                ) => {
                    f == g
                        && u == v
                        && left_args.len() == right_args.len()
                        && left_args
                            .iter()
                            .zip(&right_args)
                            .all(|(a, b)| self.root(*a) == self.root(*b))
                }
                _ => false,
            },
        )
    }

    pub fn saturate(&mut self, context: &mut Context) -> Result<(), Error> {
        loop {
            let mut changed = false;
            for left in 0..self.nodes.len() {
                let Some((f, a)) = self.nodes[left].application else {
                    continue;
                };
                for right in 0..left {
                    context.tick()?;
                    let Some((g, b)) = self.nodes[right].application else {
                        continue;
                    };
                    if self.root(left) == self.root(right)
                        || self.root(f) != self.root(g)
                        || self.root(a) != self.root(b)
                        || !self.function_congruence(context, f, g)?
                        || !convert(context, &self.nodes[left].type_, &self.nodes[right].type_)?
                    {
                        continue;
                    }
                    let fty = normalize(context, &self.nodes[f].type_)?;
                    let ExprNode::ForallE {
                        binder_type, body, ..
                    } = fty.node()
                    else {
                        continue;
                    };
                    // A dependent codomain needs heterogeneous transport when
                    // the argument changes; that larger fragment is not guessed.
                    if a != b && body.has_loose_bvars() {
                        continue;
                    }
                    let first = if f == g {
                        equality::reflexivity(
                            self.nodes[left].level.clone(),
                            self.nodes[left].type_.clone(),
                            self.nodes[left].term.clone(),
                        )
                    } else {
                        let proof = self.explain(context, f, g)?.ok_or_else(unsupported)?;
                        let variable = context.equality_local(fty.clone())?;
                        let selector = context.close_equality_binder(
                            &variable,
                            Expr::app(Expr::fvar(variable.id.clone()), self.nodes[a].term.clone()),
                            true,
                        )?;
                        context
                            .selector_congruence(
                                &Typed {
                                    value: proof,
                                    type_: equality::equation(
                                        self.nodes[f].level.clone(),
                                        fty.clone(),
                                        self.nodes[f].term.clone(),
                                        self.nodes[g].term.clone(),
                                    ),
                                },
                                &self.nodes[left].type_,
                                &self.nodes[left].level,
                                &selector,
                            )?
                            .value
                    };
                    let proof = if a == b {
                        first
                    } else {
                        let arg = self.explain(context, a, b)?.ok_or_else(unsupported)?;
                        let second = context
                            .selector_congruence(
                                &Typed {
                                    value: arg,
                                    type_: equality::equation(
                                        self.nodes[a].level.clone(),
                                        binder_type.clone(),
                                        self.nodes[a].term.clone(),
                                        self.nodes[b].term.clone(),
                                    ),
                                },
                                &self.nodes[left].type_,
                                &self.nodes[left].level,
                                &self.nodes[g].term,
                            )?
                            .value;
                        apply(
                            Expr::const_(name("Eq.trans"), vec![self.nodes[left].level.clone()]),
                            [
                                self.nodes[left].type_.clone(),
                                self.nodes[left].term.clone(),
                                Expr::app(self.nodes[g].term.clone(), self.nodes[a].term.clone()),
                                self.nodes[right].term.clone(),
                                first,
                                second,
                            ],
                        )
                    };
                    changed |= self.join(context, left, right, proof)?;
                }
            }
            if !changed {
                return Ok(());
            }
        }
    }
}
