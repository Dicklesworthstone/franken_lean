//! `buildNormProof` and `abstractAtoms` from the pinned AC tactic, using its
//! admitted reflection theorem. The host computes a candidate list normal form;
//! `eq_of_norm` must independently reduce the reflected equality to `true`.

use super::*;
use fln_core::expr::NatLit;

enum Tree {
    Atom(Expr),
    Operation(usize, usize),
}

fn reflected_variable(index: usize) -> Expr {
    Expr::app(
        Expr::const_(name("Lean.Data.AC.Expr.var"), vec![]),
        Expr::lit(Literal::Nat(NatLit::from_u64(index as u64))),
    )
}

fn reflected_operation(left: Expr, right: Expr) -> Expr {
    apply(
        Expr::const_(name("Lean.Data.AC.Expr.op"), vec![]),
        [left, right],
    )
}

fn lifted_option(type_: Expr, value: Option<Expr>) -> Expr {
    let lifted = Expr::app(
        Expr::const_(name("PLift"), vec![Level::zero()]),
        type_.clone(),
    );
    match value {
        None => Expr::app(
            Expr::const_(name("Option.none"), vec![Level::zero()]),
            lifted,
        ),
        Some(value) => apply(
            Expr::const_(name("Option.some"), vec![Level::zero()]),
            [
                lifted,
                apply(
                    Expr::const_(name("PLift.up"), vec![Level::zero()]),
                    [type_, value],
                ),
            ],
        ),
    }
}

impl Context {
    fn ac_same_operator(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if left == right {
            return Ok(true);
        }
        let mut budget = self.ambient_budget(UnificationTransparency::Default);
        budget.max_assignments = 0;
        self.proof_types_match_with_budget(left, right, budget)
    }

    fn ac_tree(
        &mut self,
        root: &Expr,
        operator: &Expr,
    ) -> Result<(Vec<Tree>, Vec<Expr>), NatDefinitionElabError> {
        enum Task {
            Visit(Expr),
            Join,
        }
        let mut pending = vec![Task::Visit(root.clone())];
        let mut nodes = Vec::new();
        let mut values = Vec::new();
        let mut atoms = Vec::new();
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Visit(term) => {
                    if let Some((head, left, right)) = binary(&term)
                        && self.ac_same_operator(operator, head)?
                    {
                        pending.push(Task::Join);
                        pending.push(Task::Visit(right.clone()));
                        pending.push(Task::Visit(left.clone()));
                        continue;
                    }
                    if !atoms.contains(&term) {
                        atoms.push(term.clone());
                    }
                    values.push(nodes.len());
                    nodes.push(Tree::Atom(term));
                }
                Task::Join => {
                    let right = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let left = values
                        .pop()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    values.push(nodes.len());
                    nodes.push(Tree::Operation(left, right));
                }
            }
            if nodes.len() > MAX_AC_NODES {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
        }
        // The pin uses insertionSort Expr.lt, independent of local-context
        // declaration order. The same comparator already orders simp's atoms.
        for index in 1..atoms.len() {
            let mut position = index;
            while position > 0 {
                self.tick()?;
                if !rewrite::ac_expr_lt(&atoms[position], &atoms[position - 1]) {
                    break;
                }
                atoms.swap(position, position - 1);
                position -= 1;
            }
        }
        Ok((nodes, atoms))
    }

    pub(super) fn ac_normalize_operator(
        &mut self,
        original: &Expr,
        laws: &Laws,
    ) -> Result<(Expr, Option<Expr>), NatDefinitionElabError> {
        let (tree, atoms) = self.ac_tree(original, &laws.operator)?;
        if atoms.is_empty() {
            return Err(failure(SourceInferenceError::Scope));
        }
        let indices: HashMap<_, _> = atoms
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, atom)| (atom, i))
            .collect();
        let mut identities = Vec::new();
        for atom in &atoms {
            self.tick()?;
            let target = apply(
                Expr::const_(name("Std.LawfulIdentity"), vec![laws.level.clone()]),
                [laws.alpha.clone(), laws.operator.clone(), atom.clone()],
            );
            identities.push(self.ac_instance(target)?);
        }
        let mut flat = Vec::new();
        let mut pending = vec![tree.len() - 1];
        while let Some(index) = pending.pop() {
            self.tick()?;
            match &tree[index] {
                Tree::Atom(atom) => flat.push(indices[atom]),
                Tree::Operation(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
            }
        }
        let first = *flat
            .first()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        flat.retain(|index| identities[*index].is_none());
        if flat.is_empty() {
            flat.push(first);
        }
        if laws.commutative.is_some() {
            flat.sort_unstable();
        }
        if laws.idempotent.is_some() {
            flat.dedup();
        }
        let mut reversed = flat.iter().rev();
        let last = *reversed
            .next()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let mut normalized = atoms[last].clone();
        for index in reversed {
            self.tick()?;
            normalized = apply(laws.operator.clone(), [atoms[*index].clone(), normalized]);
        }
        if normalized == *original {
            return Ok((normalized, None));
        }
        let proof = self.ac_certificate(laws, &tree, &atoms, &indices, &identities, &flat)?;
        Ok((normalized, Some(proof)))
    }

    fn ac_certificate(
        &mut self,
        laws: &Laws,
        tree: &[Tree],
        atoms: &[Expr],
        indices: &HashMap<Expr, usize>,
        identities: &[Option<Expr>],
        flat: &[usize],
    ) -> Result<Expr, NatDefinitionElabError> {
        let class = |class| {
            apply(
                Expr::const_(name(class), vec![laws.level.clone()]),
                [laws.alpha.clone(), laws.operator.clone()],
            )
        };
        // Like abstractAtoms, abstract each value AND its identity evidence.
        // Kernel normalization can then inspect only the small reflection data,
        // without reducing arbitrary programs occurring as atoms.
        let mut locals = Vec::new();
        let mut arguments = Vec::new();
        let mut variables = Vec::new();
        let mut variable_records = Vec::new();
        for (atom, identity) in atoms.iter().zip(identities) {
            self.tick()?;
            let local = self.equality_local(laws.alpha.clone())?;
            let value = Expr::fvar(local.id.clone());
            locals.push(local);
            arguments.push(atom.clone());
            variables.push(value.clone());
            let identity_type = Expr::app(class("Std.LawfulIdentity"), value.clone());
            let identity = if let Some(identity) = identity {
                let local = self.equality_local(identity_type.clone())?;
                let value = Expr::fvar(local.id.clone());
                locals.push(local);
                arguments.push(identity.clone());
                Some(value)
            } else {
                None
            };
            variable_records.push(apply(
                Expr::const_(name("Lean.Data.AC.Variable.mk"), vec![laws.level.clone()]),
                [
                    laws.alpha.clone(),
                    laws.operator.clone(),
                    value,
                    lifted_option(identity_type, identity),
                ],
            ));
        }
        let variable_type = class("Lean.Data.AC.Variable");
        let mut variable_list = Expr::app(
            Expr::const_(name("List.nil"), vec![laws.level.clone()]),
            variable_type.clone(),
        );
        for variable in variable_records.into_iter().rev() {
            self.tick()?;
            variable_list = apply(
                Expr::const_(name("List.cons"), vec![laws.level.clone()]),
                [variable_type.clone(), variable, variable_list],
            );
        }
        let context = apply(
            Expr::const_(name("Lean.Data.AC.Context.mk"), vec![laws.level.clone()]),
            [
                laws.alpha.clone(),
                laws.operator.clone(),
                laws.associative.clone(),
                lifted_option(class("Std.Commutative"), laws.commutative.clone()),
                lifted_option(class("Std.IdempotentOp"), laws.idempotent.clone()),
                variable_list,
                variables[0].clone(),
            ],
        );
        let mut reflected: Vec<Expr> = Vec::new();
        let mut denoted: Vec<Expr> = Vec::new();
        for node in tree {
            self.tick()?;
            let (data, term) = match node {
                Tree::Atom(atom) => (
                    reflected_variable(indices[atom]),
                    variables[indices[atom]].clone(),
                ),
                Tree::Operation(left, right) => (
                    reflected_operation(reflected[*left].clone(), reflected[*right].clone()),
                    apply(
                        laws.operator.clone(),
                        [denoted[*left].clone(), denoted[*right].clone()],
                    ),
                ),
            };
            reflected.push(data);
            denoted.push(term);
        }
        let mut reverse = flat.iter().rev();
        let last = *reverse
            .next()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let mut normalized_data = reflected_variable(last);
        let mut normalized_term = variables[last].clone();
        for index in reverse {
            self.tick()?;
            normalized_data = reflected_operation(reflected_variable(*index), normalized_data);
            normalized_term = apply(
                laws.operator.clone(),
                [variables[*index].clone(), normalized_term],
            );
        }
        let original_data = reflected
            .pop()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let original_term = denoted
            .pop()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let truth = Expr::const_(name("Bool.true"), vec![]);
        let refl = equality::reflexivity(Level::one(), Expr::const_(name("Bool"), vec![]), truth);
        let proof = apply(
            Expr::const_(
                name("Lean.Data.AC.Context.eq_of_norm"),
                vec![laws.level.clone()],
            ),
            [
                laws.alpha.clone(),
                context,
                original_data,
                normalized_data,
                refl,
            ],
        );
        let expected = equality::equation(
            laws.level.clone(),
            laws.alpha.clone(),
            original_term,
            normalized_term,
        );
        let mut proof = apply(
            Expr::const_(name("id"), vec![Level::zero()]),
            [expected, proof],
        );
        for local in locals.into_iter().rev() {
            self.tick()?;
            proof = Expr::lam(
                local.user_name,
                local.type_,
                proof
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        Ok(apply(proof, arguments))
    }
}
