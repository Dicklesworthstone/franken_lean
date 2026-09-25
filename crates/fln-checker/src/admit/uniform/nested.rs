//! Nested inductive families, judged as the mutual block the pin elaborates.
//!
//! The pin (`inductive.cpp`, `elim_nested_inductive_fn`) replaces each nested
//! occurrence `J Ds is` in a constructor type, where `J` is an existing
//! inductive whose parameters `Ds` mention a type being defined, with an
//! auxiliary family `aux As is`. The auxiliary family's constructors are `J`'s,
//! instantiated at `Ds`; every member of `J`'s own mutual block gets one. The
//! pin checks that mutual block, then restores `J Ds` in the recursors it
//! generated and names the auxiliary ones `T.rec_1`, `T.rec_2`, ...
//!
//! This check runs the same translation, in the same order, and carries the
//! declared constructors, recursor types and rules into the auxiliary block with
//! it. The unchanged mutual reconstruction then judges them there. The rewrite
//! maps exactly the occurrences the translation recorded, back to the terms the
//! pin's restoration maps them from, and the private names it introduces are
//! refused in any declared term. So a declared recursor passes exactly when it
//! is the restoration of the recursor the mutual block determines.
use super::*;
use crate::environment::{
    ConstructorDeclaration, InductiveDeclaration, RecursorDeclaration, RecursorRule,
};
use crate::term::{TermFacts, abstract_free_with, inspect_nodes_with, inspect_with};
use crate::universe::level_roots_equal;

/// The first name component of every auxiliary family and constructor.
const AUX_PREFIX: &str = "_fln_nested";
/// The first name component of the canonical parameter locals.
const PARAMETER_PREFIX: &str = "_fln_nested_parameter";

struct Aux {
    name: WireName,
    /// `J Ds`, over the canonical parameter locals.
    key: WireExpr,
    /// Each of `J`'s constructors, with the auxiliary constructor it maps to.
    constructors: Vec<(WireName, WireName)>,
}

struct Draft {
    name: WireName,
    type_: WireExpr,
    indices: u32,
    constructors: Vec<CtorDraft>,
}

struct CtorDraft {
    name: WireName,
    index: u32,
    fields: u32,
    parameters: Vec<Binder>,
    /// The type after its parameters, open over the canonical locals.
    open: WireExpr,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Binding {
    Pi,
    Lambda,
}

/// What a node becomes in the auxiliary block.
enum Replacement {
    Rename(WireName),
    /// `aux As` applied to the verbatim trailing arguments.
    Family {
        aux: usize,
        rest: Vec<ExprId>,
    },
    /// `aux.c As` applied to the verbatim trailing arguments.
    Constructor {
        name: WireName,
        rest: Vec<ExprId>,
    },
}

enum Task {
    Enter(ExprId),
    Exit(ExprId),
    Copy(ExprId),
    CopyExit(ExprId),
    Replace(ExprId, Replacement),
}

struct Translator<'e, 'a, 'b> {
    environment: &'e ConstantEnvironment,
    audit: &'a mut Audit<'b>,
    main: WireName,
    levels: Vec<WireName>,
    parameters: Vec<Binder>,
    /// The first family's result sort, `Sort l`.
    result_sort: WireExpr,
    locals: Vec<WireName>,
    originals: Vec<WireName>,
    aux: Vec<Aux>,
    drafts: Vec<Draft>,
    /// Declared `T.rec_k` and the auxiliary recursor it names, once known.
    recursors: Vec<(WireName, WireName)>,
}

fn field_limit(observed: usize) -> InductiveVerdict {
    InductiveVerdict::Deferred(InductiveSupportLimit::FieldCount {
        observed,
        limit: MAX_NONRECURSIVE_FIELDS,
    })
}

fn push_node(nodes: &mut Vec<ExprNode>, node: ExprNode) -> Result<ExprId, InductiveVerdict> {
    if nodes.len() >= MAX_INDUCTIVE_EXPECTED_ARENA_UNITS {
        return Err(arena_limit(nodes.len()));
    }
    let id = ExprId::from_index(nodes.len()).ok_or_else(overflow)?;
    nodes.push(node);
    Ok(id)
}

fn starts_with(name: &WireName, prefix: &str) -> bool {
    matches!(name.parts().first(), Some(NamePart::Text(first)) if first == prefix)
}

impl Translator<'_, '_, '_> {
    fn budget(&self) -> TermBudget {
        self.audit.term_budget()
    }

    fn free(name: &WireName) -> Result<WireExpr, InductiveVerdict> {
        let mut builder = StructuralTermBuilder::new();
        let root = builder.expression(ExprNode::Free { name: name.clone() });
        builder.finish(root).ok_or_else(overflow)
    }

    /// Peel `count` binders of one kind, keeping each as written, and open the
    /// body over the canonical locals.
    fn open(
        &mut self,
        term: &WireExpr,
        count: usize,
        binding: Binding,
        name: &WireName,
    ) -> Result<(Vec<Binder>, WireExpr), InductiveVerdict> {
        let mut binders = Vec::with_capacity(count);
        let mut tail = term.root();
        for _ in 0..count {
            self.audit.tick()?;
            let (binder_name, binder_type, body, style) = match (term.node(tail), binding) {
                (
                    Some(ExprNode::Forall {
                        binder_name,
                        binder_type,
                        body,
                        style,
                    }),
                    Binding::Pi,
                )
                | (
                    Some(ExprNode::Lambda {
                        binder_name,
                        binder_type,
                        body,
                        style,
                    }),
                    Binding::Lambda,
                ) => (binder_name, *binder_type, *body, *style),
                _ => return Err(constructor_error(name)),
            };
            binders.push(Binder {
                name: binder_name.clone(),
                style,
                domain: self.audit.piece(term, binder_type)?,
            });
            tail = body;
        }
        let mut open = self.audit.piece(term, tail)?;
        for local in self.locals[..count].iter().rev() {
            self.audit.tick()?;
            let value = Self::free(local)?;
            open = Audit::term(substitute_bound_with(
                &open,
                0,
                &value,
                self.budget(),
                &mut *self.audit.cancelled,
            ))?;
        }
        Ok((binders, open))
    }

    /// Close an open body over the canonical locals and rebuild its binders.
    fn close(
        &mut self,
        mut body: WireExpr,
        binders: &[Binder],
        binding: Binding,
    ) -> Result<WireExpr, InductiveVerdict> {
        // Abstracting a local makes it index 0 and raises those abstracted before
        // it, so the outermost parameter goes first and ends outermost.
        for local in &self.locals[..binders.len()] {
            self.audit.tick()?;
            body = Audit::term(abstract_free_with(
                &body,
                local,
                self.budget(),
                &mut *self.audit.cancelled,
            ))?;
        }
        let mut builder = StructuralTermBuilder::new();
        let mut root = self.audit.import(&mut builder, &body)?;
        for binder in binders.iter().rev() {
            let domain = self.audit.import(&mut builder, &binder.domain)?;
            root = match binding {
                Binding::Pi => builder.forall_name(&binder.name, binder.style, domain, root),
                Binding::Lambda => builder.lambda_name(&binder.name, binder.style, domain, root),
            };
        }
        self.audit.finish(builder, root)
    }

    /// Whether each node mentions one of the families being defined. Auxiliary
    /// names never occur in a term before it is rewritten, so the originals
    /// decide exactly what the pin's test over all new types decides.
    fn mentions(&mut self, term: &WireExpr) -> Result<Vec<bool>, InductiveVerdict> {
        let mut mentions = Vec::with_capacity(term.nodes().len());
        for node in term.nodes() {
            self.audit.tick()?;
            let child = |id: &ExprId| mentions.get(id.index()).copied().unwrap_or(false);
            let yes = match node {
                ExprNode::Constant { name, .. } => self.originals.contains(name),
                ExprNode::Apply { function, argument } => child(function) || child(argument),
                ExprNode::Lambda {
                    binder_type, body, ..
                }
                | ExprNode::Forall {
                    binder_type, body, ..
                } => child(binder_type) || child(body),
                ExprNode::Let {
                    type_, value, body, ..
                } => child(type_) || child(value) || child(body),
                ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                    child(expression)
                }
                ExprNode::Bound { .. }
                | ExprNode::Free { .. }
                | ExprNode::Meta { .. }
                | ExprNode::Sort { .. }
                | ExprNode::NatLiteral { .. }
                | ExprNode::StringLiteral(_) => false,
            };
            mentions.push(yes);
        }
        Ok(mentions)
    }

    /// `term` with its head constant renamed.
    fn renamed_head(term: &WireExpr, name: &WireName) -> Option<WireExpr> {
        let mut head = term.root();
        while let Some(ExprNode::Apply { function, .. }) = term.node(head) {
            head = *function;
        }
        let mut nodes = term.nodes().to_vec();
        let ExprNode::Constant { levels, .. } = nodes.get(head.index())?.clone() else {
            return None;
        };
        nodes[head.index()] = ExprNode::Constant {
            name: name.clone(),
            levels,
        };
        Some(WireExpr::from_parts(
            nodes,
            term.levels().to_vec(),
            term.root(),
        ))
    }

    fn find_aux(&mut self, key: &WireExpr) -> Result<Option<usize>, InductiveVerdict> {
        for index in 0..self.aux.len() {
            self.audit.tick()?;
            let candidate = self.aux[index].key.clone();
            if self.audit.equal(&candidate, key)? {
                return Ok(Some(index));
            }
        }
        Ok(None)
    }

    /// Instantiate a constant of `J`'s block at the occurrence's universes and at
    /// `Ds`, leaving what follows the parameters.
    fn instantiate(
        &mut self,
        declaration: &ConstantDeclaration,
        key: &WireExpr,
        roots: &[LevelId],
        ds: &[WireExpr],
        name: &WireName,
    ) -> Result<WireExpr, InductiveVerdict> {
        self.audit.tick()?;
        let term = instantiate_levels(
            declaration.type_(),
            declaration.level_parameters(),
            key.levels(),
            roots,
        )
        .ok_or_else(|| constructor_error(name))?;
        let (_, tail) =
            peel_binders_at(&term, term.root(), ds.len()).ok_or_else(|| constructor_error(name))?;
        let mut body = self.audit.piece(&term, tail)?;
        for value in ds.iter().rev() {
            self.audit.tick()?;
            body = Audit::term(substitute_bound_with(
                &body,
                0,
                value,
                self.budget(),
                &mut *self.audit.cancelled,
            ))?;
        }
        Ok(body)
    }

    /// `Π is, Sort l'` with `Sort l'` replaced by the block's `Sort l` when the
    /// two levels are equivalent. An instantiated `J` can state its universe its
    /// own way, and `mk_max` does not reorder (`Type (max b a)` at `a, b := u, v`
    /// is `max v u` where the block says `max u v`). The pin compares the levels
    /// by equivalence (`is_def_eq`); the mutual reconstruction compares result
    /// sorts structurally. A level that is not equivalent is left alone, so the
    /// block still refuses it, as the pin does.
    fn aligned_sort(
        &mut self,
        body: WireExpr,
        indices: usize,
    ) -> Result<WireExpr, InductiveVerdict> {
        let (binders, tail) = self.audit.peel(&body, indices)?;
        let (Some(ExprNode::Sort { level }), Some(ExprNode::Sort { level: expected })) = (
            tail.node(tail.root()),
            self.result_sort.node(self.result_sort.root()),
        ) else {
            return Ok(body);
        };
        if !level_roots_equal(tail.levels(), *level, self.result_sort.levels(), *expected)
            .unwrap_or(false)
        {
            return Ok(body);
        }
        let sort = self.result_sort.clone();
        let mut builder = StructuralTermBuilder::new();
        let mut root = self.audit.import(&mut builder, &sort)?;
        for binder in binders.iter().rev() {
            let domain = self.audit.import(&mut builder, &binder.domain)?;
            root = builder.forall_name(&binder.name, binder.style, domain, root);
        }
        self.audit.finish(builder, root)
    }

    /// Add an auxiliary family for every member of `J`'s block, at `Ds`, and
    /// return the one standing for `J`.
    fn create(&mut self, key: &WireExpr, inductive: &WireName) -> Result<usize, InductiveVerdict> {
        let declaration = self
            .environment
            .find(inductive)
            .ok_or_else(|| constructor_error(&self.main))?;
        let metadata = declaration
            .inductive_metadata()
            .ok_or_else(|| constructor_error(&self.main))?;
        let k = metadata.num_parameters() as usize;
        // `key` is `J Ds`: its head's universes and its k arguments.
        let mut arguments = Vec::with_capacity(k);
        let mut head = key.root();
        while let Some(ExprNode::Apply { function, argument }) = key.node(head) {
            arguments.push(*argument);
            head = *function;
        }
        arguments.reverse();
        let Some(ExprNode::Constant { levels: roots, .. }) = key.node(head) else {
            return Err(constructor_error(&self.main));
        };
        let roots = roots.clone();
        if arguments.len() != k {
            return Err(constructor_error(&self.main));
        }
        let mut ds = Vec::with_capacity(k);
        for argument in arguments {
            ds.push(self.audit.piece(key, argument)?);
        }
        let mut result = None;
        for member in metadata.mutual().to_vec() {
            self.audit.tick()?;
            let member_declaration = self
                .environment
                .find(&member)
                .ok_or_else(|| constructor_error(&self.main))?;
            let member_metadata = member_declaration
                .inductive_metadata()
                .ok_or_else(|| constructor_error(&self.main))?;
            if member_metadata.num_parameters() as usize != k {
                return Err(constructor_error(&self.main));
            }
            let name = checker_child(&checker_atom(AUX_PREFIX), &(self.aux.len() + 1).to_string());
            let member_key =
                Self::renamed_head(key, &member).ok_or_else(|| constructor_error(&self.main))?;
            let body = self.instantiate(member_declaration, key, &roots, &ds, &member)?;
            let body = self.aligned_sort(body, member_metadata.num_indices() as usize)?;
            let parameters = self.parameters.clone();
            let type_ = self.close(body, &parameters, Binding::Pi)?;
            let mut constructors = Vec::new();
            let mut drafts = Vec::new();
            for constructor in member_metadata.constructors().to_vec() {
                self.audit.tick()?;
                let constructor_declaration = self
                    .environment
                    .find(&constructor)
                    .ok_or_else(|| constructor_error(&self.main))?;
                let constructor_metadata = constructor_declaration
                    .constructor_metadata()
                    .ok_or_else(|| constructor_error(&constructor))?;
                let Some(NamePart::Text(last)) = constructor.parts().last() else {
                    return Err(constructor_error(&constructor));
                };
                let aux_constructor = checker_child(&name, last);
                let open =
                    self.instantiate(constructor_declaration, key, &roots, &ds, &constructor)?;
                constructors.push((constructor.clone(), aux_constructor.clone()));
                drafts.push(CtorDraft {
                    name: aux_constructor,
                    index: constructor_metadata.index(),
                    fields: constructor_metadata.num_fields(),
                    parameters: self.parameters.clone(),
                    open,
                });
            }
            if &member == inductive {
                result = Some(self.aux.len());
            }
            self.aux.push(Aux {
                name: name.clone(),
                key: member_key,
                constructors,
            });
            self.drafts.push(Draft {
                name,
                type_,
                indices: member_metadata.num_indices(),
                constructors: drafts,
            });
            if self.drafts.len() > MAX_MUTUAL_TYPES {
                return Err(InductiveVerdict::Deferred(
                    InductiveSupportLimit::MultipleTypes {
                        observed: self.drafts.len(),
                    },
                ));
            }
        }
        result.ok_or_else(|| constructor_error(&self.main))
    }

    /// The application spine at `id`: the node for each prefix, outermost
    /// first, the head, and the arguments in order.
    fn spine(term: &WireExpr, id: ExprId) -> (Vec<ExprId>, ExprId, Vec<ExprId>) {
        let mut prefixes = Vec::new();
        let mut arguments = Vec::new();
        let mut head = id;
        while let Some(ExprNode::Apply { function, argument }) = term.node(head) {
            prefixes.push(head);
            arguments.push(*argument);
            head = *function;
        }
        arguments.reverse();
        (prefixes, head, arguments)
    }

    /// What `id` becomes, if the translation replaces it.
    fn replacement(
        &mut self,
        term: &WireExpr,
        facts: &[TermFacts],
        mentions: &[bool],
        id: ExprId,
        recursor: bool,
    ) -> Result<Option<Replacement>, InductiveVerdict> {
        match term.node(id) {
            Some(ExprNode::Constant { name, .. }) if recursor => {
                return Ok(self
                    .recursors
                    .iter()
                    .find(|(declared, _)| declared == name)
                    .map(|(_, aux)| Replacement::Rename(aux.clone())));
            }
            Some(ExprNode::Apply { .. }) => {}
            _ => return Ok(None),
        }
        if !mentions.get(id.index()).copied().unwrap_or(false) {
            return Ok(None);
        }
        let (prefixes, head, arguments) = Self::spine(term, id);
        let Some(ExprNode::Constant { name, .. }) = term.node(head) else {
            return Ok(None);
        };
        let Some(declaration) = self.environment.find(name) else {
            return Ok(None);
        };
        if let Some(metadata) = declaration.inductive_metadata() {
            let k = metadata.num_parameters() as usize;
            if k == 0 || arguments.len() < k {
                return Ok(None);
            }
            // The prefix `J Ds`: the node applying exactly the k parameters.
            let prefix = prefixes[arguments.len() - k];
            if !arguments[..k]
                .iter()
                .any(|argument| mentions.get(argument.index()).copied().unwrap_or(false))
            {
                return Ok(None);
            }
            if facts
                .get(prefix.index())
                .is_none_or(|facts| facts.external_bound_span != 0)
            {
                // The pin: nested parameters cannot contain local variables.
                return Err(constructor_error(&self.main));
            }
            let key = self.audit.piece(term, prefix)?;
            let aux = match self.find_aux(&key)? {
                Some(aux) => aux,
                None if !recursor => {
                    let inductive = name.clone();
                    self.create(&key, &inductive)?
                }
                None => return Ok(None),
            };
            return Ok(Some(Replacement::Family {
                aux,
                rest: arguments[k..].to_vec(),
            }));
        }
        if !recursor {
            return Ok(None);
        }
        let Some(metadata) = declaration.constructor_metadata() else {
            return Ok(None);
        };
        let k = metadata.num_parameters() as usize;
        if k == 0 || arguments.len() < k {
            return Ok(None);
        }
        let prefix = prefixes[arguments.len() - k];
        let piece = self.audit.piece(term, prefix)?;
        let Some(key) = Self::renamed_head(&piece, metadata.inductive()) else {
            return Ok(None);
        };
        let Some(aux) = self.find_aux(&key)? else {
            return Ok(None);
        };
        let Some((_, constructor)) = self.aux[aux]
            .constructors
            .iter()
            .find(|(declared, _)| declared == name)
        else {
            return Ok(None);
        };
        Ok(Some(Replacement::Constructor {
            name: constructor.clone(),
            rest: arguments[k..].to_vec(),
        }))
    }

    /// Carry `term` into the auxiliary block. Pre-order, as the pin's `replace`:
    /// a replaced node's arguments are kept verbatim, never visited, so
    /// auxiliary families are discovered in the pin's order.
    fn rewrite(&mut self, term: &WireExpr, recursor: bool) -> Result<WireExpr, InductiveVerdict> {
        let facts = match inspect_nodes_with(term, self.budget(), &mut *self.audit.cancelled) {
            TermOutcome::Complete(facts) => facts,
            TermOutcome::Inconclusive(stop) => {
                return Err(InductiveVerdict::Inconclusive(InductiveStop::Term(stop)));
            }
            TermOutcome::InternalFault(fault) => {
                return Err(InductiveVerdict::InternalFault(InductiveFault::Term(fault)));
            }
        };
        let mentions = self.mentions(term)?;
        let count = term.nodes().len();
        let mut rewritten: Vec<Option<ExprId>> = vec![None; count];
        let mut copied: Vec<Option<ExprId>> = vec![None; count];
        let mut nodes: Vec<ExprNode> = Vec::new();
        let mut levels: Vec<LevelNode> = term.levels().to_vec();
        let mut block_levels: Option<Vec<LevelId>> = None;
        let mut locals: Option<Vec<ExprId>> = None;
        let mut tasks = vec![Task::Enter(term.root())];
        while let Some(task) = tasks.pop() {
            self.audit.tick()?;
            match task {
                Task::Enter(id) => {
                    if rewritten.get(id.index()).copied().flatten().is_some() {
                        continue;
                    }
                    if let Some(replacement) =
                        self.replacement(term, &facts, &mentions, id, recursor)?
                    {
                        let rest = match &replacement {
                            Replacement::Rename(_) => Vec::new(),
                            Replacement::Family { rest, .. }
                            | Replacement::Constructor { rest, .. } => rest.clone(),
                        };
                        tasks.push(Task::Replace(id, replacement));
                        for argument in rest.into_iter().rev() {
                            tasks.push(Task::Copy(argument));
                        }
                        continue;
                    }
                    tasks.push(Task::Exit(id));
                    let node = term.node(id).ok_or_else(overflow)?;
                    for child in children(node).into_iter().rev() {
                        tasks.push(Task::Enter(child));
                    }
                }
                Task::Copy(id) => {
                    if copied.get(id.index()).copied().flatten().is_some() {
                        continue;
                    }
                    tasks.push(Task::CopyExit(id));
                    let node = term.node(id).ok_or_else(overflow)?;
                    for child in children(node).into_iter().rev() {
                        tasks.push(Task::Copy(child));
                    }
                }
                Task::Exit(id) | Task::CopyExit(id) => {
                    let table = if matches!(task, Task::Exit(_)) {
                        &rewritten
                    } else {
                        &copied
                    };
                    let node = term.node(id).ok_or_else(overflow)?;
                    let mapped =
                        map_children(node, |child| table.get(child.index()).copied().flatten())
                            .ok_or_else(overflow)?;
                    let new = push_node(&mut nodes, mapped)?;
                    let slot = if matches!(task, Task::Exit(_)) {
                        &mut rewritten
                    } else {
                        &mut copied
                    };
                    if let Some(slot) = slot.get_mut(id.index()) {
                        *slot = Some(new);
                    }
                }
                Task::Replace(id, replacement) => {
                    let block_levels = match &block_levels {
                        Some(ids) => ids.clone(),
                        None => {
                            let mut ids = Vec::with_capacity(self.levels.len());
                            for parameter in &self.levels {
                                let level =
                                    LevelId::from_index(levels.len()).ok_or_else(overflow)?;
                                levels.push(LevelNode::Parameter(parameter.clone()));
                                ids.push(level);
                            }
                            block_levels = Some(ids.clone());
                            ids
                        }
                    };
                    let new = match replacement {
                        Replacement::Rename(name) => {
                            let Some(ExprNode::Constant { levels: ids, .. }) = term.node(id) else {
                                return Err(overflow());
                            };
                            push_node(
                                &mut nodes,
                                ExprNode::Constant {
                                    name,
                                    levels: ids.clone(),
                                },
                            )?
                        }
                        Replacement::Family { aux, rest } => {
                            let name = self.aux[aux].name.clone();
                            self.applied(
                                &mut nodes,
                                &mut locals,
                                name,
                                block_levels,
                                &rest,
                                &copied,
                            )?
                        }
                        Replacement::Constructor { name, rest } => self.applied(
                            &mut nodes,
                            &mut locals,
                            name,
                            block_levels,
                            &rest,
                            &copied,
                        )?,
                    };
                    if let Some(slot) = rewritten.get_mut(id.index()) {
                        *slot = Some(new);
                    }
                }
            }
        }
        let root = rewritten
            .get(term.root().index())
            .copied()
            .flatten()
            .ok_or_else(overflow)?;
        Ok(WireExpr::from_parts(nodes, levels, root))
    }

    /// `name{block levels} As rest`, with `As` the canonical locals.
    fn applied(
        &self,
        nodes: &mut Vec<ExprNode>,
        locals: &mut Option<Vec<ExprId>>,
        name: WireName,
        levels: Vec<LevelId>,
        rest: &[ExprId],
        copied: &[Option<ExprId>],
    ) -> Result<ExprId, InductiveVerdict> {
        let local_ids = match locals {
            Some(ids) => ids.clone(),
            None => {
                let mut ids = Vec::with_capacity(self.locals.len());
                for local in &self.locals {
                    ids.push(push_node(
                        nodes,
                        ExprNode::Free {
                            name: local.clone(),
                        },
                    )?);
                }
                *locals = Some(ids.clone());
                ids
            }
        };
        let mut result = push_node(nodes, ExprNode::Constant { name, levels })?;
        for local in local_ids {
            result = push_node(
                nodes,
                ExprNode::Apply {
                    function: result,
                    argument: local,
                },
            )?;
        }
        for argument in rest {
            let argument = copied
                .get(argument.index())
                .copied()
                .flatten()
                .ok_or_else(overflow)?;
            result = push_node(
                nodes,
                ExprNode::Apply {
                    function: result,
                    argument,
                },
            )?;
        }
        Ok(result)
    }
}

/// The pin's `instantiate_lparams` (`level.cpp`, `instantiate` over `replace`):
/// a level containing none of `parameters` is kept exactly as written; any
/// other is rebuilt, and every rebuilt `max` and `imax` goes through `mk_max`
/// and `mk_imax`, which simplify. Instantiating without those simplifications
/// leaves `max 0 0` where the pin wrote `0`, and the nested occurrences it
/// restores into the recursors would no longer be the ones recorded here.
fn instantiate_levels(
    term: &WireExpr,
    parameters: &[WireName],
    values: &[LevelNode],
    roots: &[LevelId],
) -> Option<WireExpr> {
    if parameters.len() != roots.len() {
        return None;
    }
    let mut out = Levels { nodes: Vec::new() };
    let mut imported: Vec<Option<LevelId>> = vec![None; values.len()];
    let mut value_ids = Vec::with_capacity(roots.len());
    for root in roots {
        value_ids.push(out.import(values, *root, &mut imported)?);
    }
    let source = term.levels();
    let mut mapped: Vec<LevelId> = Vec::with_capacity(source.len());
    let mut changed: Vec<bool> = Vec::with_capacity(source.len());
    for node in source {
        let child = |id: &LevelId| -> Option<(LevelId, bool)> {
            Some((*mapped.get(id.index())?, *changed.get(id.index())?))
        };
        let (id, moved) = match node {
            LevelNode::Parameter(name) => match parameters.iter().position(|p| p == name) {
                Some(index) => (value_ids[index], true),
                None => (out.push(node.clone())?, false),
            },
            LevelNode::Zero | LevelNode::Meta(_) => (out.push(node.clone())?, false),
            LevelNode::Succ(inner) => {
                let (inner, moved) = child(inner)?;
                (out.push(LevelNode::Succ(inner))?, moved)
            }
            LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                let (left, left_moved) = child(left)?;
                let (right, right_moved) = child(right)?;
                let is_max = matches!(node, LevelNode::Max(..));
                if !left_moved && !right_moved {
                    let node = if is_max {
                        LevelNode::Max(left, right)
                    } else {
                        LevelNode::IMax(left, right)
                    };
                    (out.push(node)?, false)
                } else if is_max {
                    (out.max(left, right)?, true)
                } else {
                    (out.imax(left, right)?, true)
                }
            }
        };
        mapped.push(id);
        changed.push(moved);
    }
    let level = |id: &LevelId| mapped.get(id.index()).copied();
    let nodes = term
        .nodes()
        .iter()
        .map(|node| {
            Some(match node {
                ExprNode::Sort { level: id } => ExprNode::Sort { level: level(id)? },
                ExprNode::Constant { name, levels } => ExprNode::Constant {
                    name: name.clone(),
                    levels: levels.iter().map(level).collect::<Option<Vec<_>>>()?,
                },
                other => other.clone(),
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(WireExpr::from_parts(nodes, out.nodes, term.root()))
}

/// A level arena with the pin's smart constructors.
struct Levels {
    nodes: Vec<LevelNode>,
}

impl Levels {
    fn push(&mut self, node: LevelNode) -> Option<LevelId> {
        let id = LevelId::from_index(self.nodes.len())?;
        self.nodes.push(node);
        Some(id)
    }

    fn import(
        &mut self,
        source: &[LevelNode],
        root: LevelId,
        imported: &mut Vec<Option<LevelId>>,
    ) -> Option<LevelId> {
        if let Some(id) = imported.get(root.index()).copied().flatten() {
            return Some(id);
        }
        let node = match source.get(root.index())? {
            LevelNode::Succ(inner) if inner.index() < root.index() => {
                LevelNode::Succ(self.import(source, *inner, imported)?)
            }
            LevelNode::Max(left, right)
                if left.index() < root.index() && right.index() < root.index() =>
            {
                LevelNode::Max(
                    self.import(source, *left, imported)?,
                    self.import(source, *right, imported)?,
                )
            }
            LevelNode::IMax(left, right)
                if left.index() < root.index() && right.index() < root.index() =>
            {
                LevelNode::IMax(
                    self.import(source, *left, imported)?,
                    self.import(source, *right, imported)?,
                )
            }
            LevelNode::Zero => LevelNode::Zero,
            LevelNode::Parameter(name) => LevelNode::Parameter(name.clone()),
            LevelNode::Meta(name) => LevelNode::Meta(name.clone()),
            _ => return None,
        };
        let id = self.push(node)?;
        if let Some(slot) = imported.get_mut(root.index()) {
            *slot = Some(id);
        }
        Some(id)
    }

    fn node(&self, id: LevelId) -> Option<&LevelNode> {
        self.nodes.get(id.index())
    }

    /// Structural equality, `level::operator==`.
    fn equal(&self, left: LevelId, right: LevelId) -> bool {
        if left == right {
            return true;
        }
        match (self.node(left), self.node(right)) {
            (Some(LevelNode::Zero), Some(LevelNode::Zero)) => true,
            (Some(LevelNode::Parameter(a)), Some(LevelNode::Parameter(b)))
            | (Some(LevelNode::Meta(a)), Some(LevelNode::Meta(b))) => a == b,
            (Some(LevelNode::Succ(a)), Some(LevelNode::Succ(b))) => self.equal(*a, *b),
            (Some(LevelNode::Max(a, b)), Some(LevelNode::Max(c, d)))
            | (Some(LevelNode::IMax(a, b)), Some(LevelNode::IMax(c, d))) => {
                self.equal(*a, *c) && self.equal(*b, *d)
            }
            _ => false,
        }
    }

    fn is_zero(&self, id: LevelId) -> bool {
        matches!(self.node(id), Some(LevelNode::Zero))
    }

    /// `is_explicit`: `succ^k 0`, returning `k`.
    fn explicit(&self, mut id: LevelId) -> Option<usize> {
        let mut depth = 0usize;
        loop {
            match self.node(id)? {
                LevelNode::Zero => return Some(depth),
                LevelNode::Succ(inner) => {
                    depth += 1;
                    id = *inner;
                }
                _ => return None,
            }
        }
    }

    /// `to_offset`: `succ^k l` as `(l, k)`.
    fn offset(&self, mut id: LevelId) -> (LevelId, usize) {
        let mut k = 0usize;
        while let Some(LevelNode::Succ(inner)) = self.node(id) {
            id = *inner;
            k += 1;
        }
        (id, k)
    }

    /// `is_not_zero`.
    fn not_zero(&self, id: LevelId) -> bool {
        match self.node(id) {
            Some(LevelNode::Succ(_)) => true,
            Some(LevelNode::Max(a, b)) => self.not_zero(*a) || self.not_zero(*b),
            Some(LevelNode::IMax(_, b)) => self.not_zero(*b),
            _ => false,
        }
    }

    /// `mk_max` (`level.cpp`).
    fn max(&mut self, left: LevelId, right: LevelId) -> Option<LevelId> {
        if let (Some(a), Some(b)) = (self.explicit(left), self.explicit(right)) {
            return Some(if a >= b { left } else { right });
        }
        if self.equal(left, right) || self.is_zero(right) {
            return Some(left);
        }
        if self.is_zero(left) {
            return Some(right);
        }
        if let Some(LevelNode::Max(a, b)) = self.node(right).cloned()
            && (self.equal(a, left) || self.equal(b, left))
        {
            return Some(right);
        }
        if let Some(LevelNode::Max(a, b)) = self.node(left).cloned()
            && (self.equal(a, right) || self.equal(b, right))
        {
            return Some(left);
        }
        let (base_left, k_left) = self.offset(left);
        let (base_right, k_right) = self.offset(right);
        if self.equal(base_left, base_right) {
            return Some(if k_left > k_right { left } else { right });
        }
        self.push(LevelNode::Max(left, right))
    }

    /// `mk_imax` (`level.cpp`).
    fn imax(&mut self, left: LevelId, right: LevelId) -> Option<LevelId> {
        if self.not_zero(right) {
            return self.max(left, right);
        }
        if self.is_zero(right) {
            return Some(right);
        }
        if self.is_zero(left) || self.explicit(left) == Some(1) {
            return Some(right);
        }
        if self.equal(left, right) {
            return Some(left);
        }
        self.push(LevelNode::IMax(left, right))
    }
}

fn children(node: &ExprNode) -> Vec<ExprId> {
    match node {
        ExprNode::Apply { function, argument } => vec![*function, *argument],
        ExprNode::Lambda {
            binder_type, body, ..
        }
        | ExprNode::Forall {
            binder_type, body, ..
        } => vec![*binder_type, *body],
        ExprNode::Let {
            type_, value, body, ..
        } => vec![*type_, *value, *body],
        ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
            vec![*expression]
        }
        ExprNode::Bound { .. }
        | ExprNode::Free { .. }
        | ExprNode::Meta { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Constant { .. }
        | ExprNode::NatLiteral { .. }
        | ExprNode::StringLiteral(_) => Vec::new(),
    }
}

fn map_children(
    node: &ExprNode,
    mut map: impl FnMut(ExprId) -> Option<ExprId>,
) -> Option<ExprNode> {
    Some(match node {
        ExprNode::Apply { function, argument } => ExprNode::Apply {
            function: map(*function)?,
            argument: map(*argument)?,
        },
        ExprNode::Lambda {
            binder_name,
            binder_type,
            body,
            style,
        } => ExprNode::Lambda {
            binder_name: binder_name.clone(),
            binder_type: map(*binder_type)?,
            body: map(*body)?,
            style: *style,
        },
        ExprNode::Forall {
            binder_name,
            binder_type,
            body,
            style,
        } => ExprNode::Forall {
            binder_name: binder_name.clone(),
            binder_type: map(*binder_type)?,
            body: map(*body)?,
            style: *style,
        },
        ExprNode::Let {
            declaration_name,
            type_,
            value,
            body,
            non_dependent,
        } => ExprNode::Let {
            declaration_name: declaration_name.clone(),
            type_: map(*type_)?,
            value: map(*value)?,
            body: map(*body)?,
            non_dependent: *non_dependent,
        },
        ExprNode::Metadata {
            entries,
            expression,
        } => ExprNode::Metadata {
            entries: entries.clone(),
            expression: map(*expression)?,
        },
        ExprNode::Projection {
            structure_name,
            index,
            expression,
        } => ExprNode::Projection {
            structure_name: structure_name.clone(),
            index: *index,
            expression: map(*expression)?,
        },
        leaf => leaf.clone(),
    })
}

/// A declared term may name no private auxiliary constant and hold no free
/// local, so nothing it contains can be mistaken for the translation's own.
fn private_names_absent(audit: &mut Audit<'_>, term: &WireExpr) -> Result<bool, InductiveVerdict> {
    let facts = match inspect_with(term, audit.term_budget(), &mut *audit.cancelled) {
        TermOutcome::Complete(facts) => facts,
        TermOutcome::Inconclusive(stop) => {
            return Err(InductiveVerdict::Inconclusive(InductiveStop::Term(stop)));
        }
        TermOutcome::InternalFault(fault) => {
            return Err(InductiveVerdict::InternalFault(InductiveFault::Term(fault)));
        }
    };
    if facts.contains_free {
        return Ok(false);
    }
    for node in term.nodes() {
        audit.tick()?;
        if let ExprNode::Constant { name, .. } = node
            && (starts_with(name, AUX_PREFIX) || starts_with(name, PARAMETER_PREFIX))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(in crate::admit) fn admit(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    inductive: &ConstantEntry,
    budget: AdmissionBudget,
    environment_budget: EnvironmentBudget,
    comparison: &mut StructuralComparisonControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> InductiveVerdict {
    let mut audit = Audit {
        budget,
        comparison,
        cancelled,
    };
    match check(
        environment,
        declarations,
        inductive,
        environment_budget,
        &mut audit,
    ) {
        Ok(members) => InductiveVerdict::Admitted(InductiveAdmission { members }),
        Err(verdict) => verdict,
    }
}

#[allow(clippy::too_many_lines)]
fn check(
    environment: &ConstantEnvironment,
    declarations: &[ConstantEntry],
    first: &ConstantEntry,
    environment_budget: EnvironmentBudget,
    audit: &mut Audit<'_>,
) -> Result<Vec<WireName>, InductiveVerdict> {
    audit.tick()?;
    let main = first.name().clone();
    let header = first.declaration();
    let metadata = header
        .inductive_metadata()
        .ok_or_else(|| constructor_error(&main))?;
    let originals = metadata.mutual().to_vec();
    if originals.first() != Some(&main) {
        return Err(constructor_error(&main));
    }
    let p = metadata.num_parameters() as usize;
    if p > MAX_NONRECURSIVE_FIELDS {
        return Err(field_limit(p));
    }
    for entry in declarations {
        let declaration = entry.declaration();
        let mut terms = vec![declaration.type_()];
        if let Some(recursor) = declaration.recursor_metadata() {
            terms.extend(recursor.rules().iter().map(RecursorRule::rhs));
        }
        for term in terms {
            if !private_names_absent(audit, term)? {
                return Err(constructor_error(entry.name()));
            }
        }
    }
    let find = |name: &WireName| declarations.iter().find(|entry| entry.name() == name);
    let (parameters, tail) = audit.peel(header.type_(), p)?;
    let (_, result_sort) = audit.peel(&tail, metadata.num_indices() as usize)?;
    let locals = (0..p)
        .map(|index| checker_child(&checker_atom(PARAMETER_PREFIX), &index.to_string()))
        .collect();
    let mut translator = Translator {
        environment,
        audit,
        main: main.clone(),
        levels: header.level_parameters().to_vec(),
        parameters,
        result_sort,
        locals,
        originals: originals.clone(),
        aux: Vec::new(),
        drafts: Vec::new(),
        recursors: Vec::new(),
    };
    for name in &originals {
        let entry = find(name).ok_or_else(|| constructor_error(name))?;
        let metadata = entry
            .declaration()
            .inductive_metadata()
            .ok_or_else(|| constructor_error(name))?;
        let mut constructors = Vec::new();
        for constructor in metadata.constructors() {
            let entry = find(constructor).ok_or_else(|| {
                InductiveVerdict::Rejected(InductiveRejection::ConstructorMissing {
                    name: constructor.clone(),
                })
            })?;
            let cm = entry
                .declaration()
                .constructor_metadata()
                .ok_or_else(|| constructor_error(constructor))?;
            let (parameters, open) =
                translator.open(entry.declaration().type_(), p, Binding::Pi, constructor)?;
            constructors.push(CtorDraft {
                name: constructor.clone(),
                index: cm.index(),
                fields: cm.num_fields(),
                parameters,
                open,
            });
        }
        translator.drafts.push(Draft {
            name: name.clone(),
            type_: entry.declaration().type_().clone(),
            indices: metadata.num_indices(),
            constructors,
        });
    }
    // The pin's main loop: every family, including those added on the way,
    // has each constructor translated once.
    let mut qhead = 0;
    while qhead < translator.drafts.len() {
        for index in 0..translator.drafts[qhead].constructors.len() {
            let open = translator.drafts[qhead].constructors[index].open.clone();
            let rewritten = translator.rewrite(&open, false)?;
            translator.drafts[qhead].constructors[index].open = rewritten;
        }
        qhead += 1;
    }
    let nested = translator.aux.len();
    if nested == 0 {
        return Err(constructor_error(&main));
    }
    translator.recursors = (1..=nested)
        .map(|index| {
            (
                checker_child(&main, &format!("rec_{index}")),
                checker_child(&translator.aux[index - 1].name, "rec"),
            )
        })
        .collect();
    let block: Vec<WireName> = translator
        .drafts
        .iter()
        .map(|draft| draft.name.clone())
        .collect();
    // Declared: each original family, its constructors and its recursor, and
    // one recursor per auxiliary family.
    let expected_rows = 2 * originals.len()
        + translator.drafts[..originals.len()]
            .iter()
            .map(|draft| draft.constructors.len())
            .sum::<usize>()
        + nested;
    if declarations.len() != expected_rows {
        return Err(InductiveVerdict::Rejected(
            InductiveRejection::DeclarationCount {
                observed: declarations.len(),
                expected: expected_rows,
            },
        ));
    }
    let mut synthetic = Vec::new();
    let flags = (metadata.is_recursive(), metadata.is_reflexive());
    for (position, draft) in translator.drafts.iter().enumerate() {
        let names = draft
            .constructors
            .iter()
            .map(|constructor| constructor.name.clone())
            .collect();
        let declaration = if let Some(original) = originals.get(position) {
            let entry = find(original).ok_or_else(|| constructor_error(original))?;
            let om = entry
                .declaration()
                .inductive_metadata()
                .ok_or_else(|| constructor_error(original))?;
            if om.num_nested() as usize != nested
                || om.mutual() != originals.as_slice()
                || (om.is_recursive(), om.is_reflexive()) != flags
            {
                return Err(constructor_error(original));
            }
            ConstantDeclaration::inductive(
                entry.declaration().level_parameters().to_vec(),
                draft.type_.clone(),
                entry.declaration().safety(),
                InductiveDeclaration::new(
                    om.num_parameters(),
                    om.num_indices(),
                    block.clone(),
                    names,
                    0,
                    flags.0,
                    flags.1,
                ),
            )
        } else {
            ConstantDeclaration::inductive(
                translator.levels.clone(),
                draft.type_.clone(),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    p as u32,
                    draft.indices,
                    block.clone(),
                    names,
                    0,
                    flags.0,
                    flags.1,
                ),
            )
        };
        synthetic.push(ConstantEntry::new(draft.name.clone(), declaration));
    }
    for position in 0..translator.drafts.len() {
        for index in 0..translator.drafts[position].constructors.len() {
            let family = translator.drafts[position].name.clone();
            let constructor = &translator.drafts[position].constructors[index];
            let (name, cindex, fields, parameters, open) = (
                constructor.name.clone(),
                constructor.index,
                constructor.fields,
                constructor.parameters.clone(),
                constructor.open.clone(),
            );
            let type_ = translator.close(open, &parameters, Binding::Pi)?;
            let (levels, safety) = match find(&name) {
                Some(entry) => (
                    entry.declaration().level_parameters().to_vec(),
                    entry.declaration().safety(),
                ),
                None => (translator.levels.clone(), ConstantSafety::Safe),
            };
            synthetic.push(ConstantEntry::new(
                name,
                ConstantDeclaration::constructor(
                    levels,
                    type_,
                    safety,
                    ConstructorDeclaration::new(family, cindex, p as u32, fields),
                ),
            ));
        }
    }
    let mut recursor_names: Vec<(WireName, WireName, Option<usize>)> = originals
        .iter()
        .map(|name| (checker_child(name, "rec"), checker_child(name, "rec"), None))
        .collect();
    for (index, (declared, aux)) in translator.recursors.iter().enumerate() {
        recursor_names.push((declared.clone(), aux.clone(), Some(index)));
    }
    for (declared, name, aux) in recursor_names {
        let entry = find(&declared).ok_or_else(|| {
            InductiveVerdict::Rejected(InductiveRejection::RecursorMissing {
                name: declared.clone(),
            })
        })?;
        let declaration = entry.declaration();
        let rec = declaration
            .recursor_metadata()
            .ok_or_else(|| recursor_error(&declared))?;
        if rec.mutual() != originals.as_slice() || rec.num_parameters() as usize != p {
            return Err(recursor_error(&declared));
        }
        let (binders, open) = translator.open(declaration.type_(), p, Binding::Pi, &declared)?;
        let open = translator.rewrite(&open, true)?;
        let type_ = translator.close(open, &binders, Binding::Pi)?;
        let mut rules = Vec::with_capacity(rec.rules().len());
        for rule in rec.rules() {
            let constructor = match aux {
                None => rule.constructor().clone(),
                Some(index) => translator.aux[index]
                    .constructors
                    .iter()
                    .find(|(declared, _)| declared == rule.constructor())
                    .map(|(_, aux)| aux.clone())
                    .ok_or_else(|| recursor_error(&declared))?,
            };
            let (binders, open) = translator.open(rule.rhs(), p, Binding::Lambda, &declared)?;
            let open = translator.rewrite(&open, true)?;
            let rhs = translator.close(open, &binders, Binding::Lambda)?;
            rules.push(RecursorRule::new(constructor, rule.num_fields(), rhs));
        }
        synthetic.push(ConstantEntry::new(
            name,
            ConstantDeclaration::recursor(
                declaration.level_parameters().to_vec(),
                type_,
                declaration.safety(),
                RecursorDeclaration::new(
                    block.clone(),
                    rec.num_parameters(),
                    rec.num_indices(),
                    rec.num_motives(),
                    rec.num_minors(),
                    rules,
                    rec.k(),
                ),
            ),
        ));
    }
    let first = synthetic.first().ok_or_else(overflow)?;
    super::mutual::check(
        environment,
        &synthetic,
        first,
        environment_budget,
        &mut *translator.audit,
    )?;
    Ok(declarations
        .iter()
        .map(|entry| entry.name().clone())
        .collect())
}
