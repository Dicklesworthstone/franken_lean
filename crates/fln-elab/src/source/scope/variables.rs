//! Checked, lexical section parameters. Their types are checked at the variable
//! command. The pin keeps the command's syntax and elaborates it again in each
//! declaration, so a later `open` or declaration can change what its names mean:
//! a declaration using a variable whose binder would now elaborate differently is
//! refused, never checked against the earlier reading.
//! They become ordinary Pi/lambda binders; no section state reaches admission.
use super::*;
use std::collections::{HashMap, HashSet};

pub const MAX_SECTION_VARIABLES: usize = 4096;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SectionVariables {
    locals: LocalContext,
    next: u64,
    levels: Vec<Name>,
    included: HashSet<FVarId>,
    omitted: HashSet<FVarId>,
    /// Each `variable` command's binders, with the number of section locals after it. The pin
    /// keeps this syntax (`varDecls`) and elaborates it again in every declaration.
    commands: Vec<(Syntax, usize)>,
}

impl SectionVariables {
    pub fn len(&self) -> usize {
        self.locals.len()
    }

    pub fn is_empty(&self) -> bool {
        self.locals.is_empty()
    }

    /// Every section variable in declaration order, as a term elaborated in this scope may
    /// name it; a later one with an earlier one's name shadows it.
    pub fn declared(&self) -> &[LocalDecl] {
        self.locals.decls()
    }

    /// Selection refers to declared identities, not namespace lookup or future
    /// binders. Resolve the entire command before changing either set.
    pub fn select(&mut self, names: &[Name], include: bool) -> Result<(), ScopeError> {
        if names.len() > MAX_SECTION_VARIABLES {
            return Err(ScopeError::VariableSelectionLimit);
        }
        let mut by_name: HashMap<&Name, Vec<&FVarId>> = HashMap::new();
        for local in self.locals.decls() {
            by_name.entry(&local.user_name).or_default().push(&local.id);
        }
        let mut selected = HashSet::new();
        for name in names {
            let ids = by_name
                .get(name)
                .ok_or_else(|| ScopeError::UnknownVariable(name.clone()))?;
            // Unlike term lookup and binder updates, the pin's `elabInclude`
            // uses `findIdx?` over declarations in source order. `elabOmit`
            // walks every local, so it omits every occurrence of a name.
            if include {
                selected.insert((*ids[0]).clone());
            } else {
                selected.extend(ids.iter().map(|id| (*id).clone()));
            }
        }
        for id in selected {
            if include {
                self.omitted.remove(&id);
                self.included.insert(id);
            } else {
                self.included.remove(&id);
                self.omitted.insert(id);
            }
        }
        Ok(())
    }

    pub(in crate::source) fn locals(&self) -> &LocalContext {
        &self.locals
    }

    pub(in crate::source) fn next(&self) -> u64 {
        self.next
    }

    pub(in crate::source) fn levels(&self) -> &[Name] {
        &self.levels
    }
}

/// A stored bracketed binder, before optional-parameter expansion. Annotation
/// updates rewrite this syntax too: declarations replay it in their own scope.
struct VariableBinder<'a> {
    names: &'a [Syntax],
    type_: Option<&'a Syntax>,
    style: BinderInfo,
    has_default: bool,
}

fn variable_binder(syntax: &Syntax) -> Result<VariableBinder<'_>, NatDefinitionElabError> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return Err(failure(SourceInferenceError::Scope));
    };
    if kind == &parser_kind(&["Term", "instBinder"]) {
        let [open, names, type_, close] = args.as_slice() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(open, "[", "instance binder opener")?;
        expect_atom(close, "]", "instance binder closer")?;
        let names = expect_null_args(names, "optional instance name")?;
        let names = match names {
            [] => names,
            [Syntax::Ident { .. }, colon] => {
                expect_atom(colon, ":", "instance name colon")?;
                &names[..1]
            }
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        return Ok(VariableBinder {
            names,
            type_: Some(type_),
            style: BinderInfo::InstImplicit,
            has_default: false,
        });
    }
    let (style, open, close, arity) = if kind == &parser_kind(&["Term", "implicitBinder"]) {
        (BinderInfo::Implicit, "{", "}", 4)
    } else if kind == &parser_kind(&["Term", "strictImplicitBinder"]) {
        (BinderInfo::StrictImplicit, "⦃", "⦄", 4)
    } else if kind == &parser_kind(&["Term", "explicitBinder"]) {
        (BinderInfo::Default, "(", ")", 5)
    } else {
        return Err(failure(SourceInferenceError::Scope));
    };
    let parts = expect_node(syntax, kind, arity, "section variable binder")?;
    expect_atom(&parts[0], open, "binder opener")?;
    expect_atom(&parts[arity - 1], close, "binder closer")?;
    let names = expect_null_args(&parts[1], "binder names")?;
    if names.is_empty() {
        return Err(failure(SourceInferenceError::Scope));
    }
    let type_ = match expect_null_args(&parts[2], "binder type")? {
        [] => None,
        [colon, type_] => {
            expect_atom(colon, ":", "binder type ascription")?;
            Some(type_)
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    Ok(VariableBinder {
        names,
        type_,
        style,
        has_default: arity == 5 && !expect_null_args(&parts[3], "binder default")?.is_empty(),
    })
}

fn rebuilt_binder(name: Syntax, type_: Option<&Syntax>, style: BinderInfo) -> Syntax {
    let atom = |s: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, s);
    let null = |args| Syntax::node(Name::from_components(["null"]), args);
    if style == BinderInfo::InstImplicit {
        return Syntax::node(
            parser_kind(&["Term", "instBinder"]),
            vec![
                atom("["),
                null(vec![name, atom(":")]),
                type_
                    .expect("instance updates require a written type")
                    .clone(),
                atom("]"),
            ],
        );
    }
    let (kind, open, close) = match style {
        BinderInfo::Default => ("explicitBinder", "(", ")"),
        BinderInfo::Implicit => ("implicitBinder", "{", "}"),
        BinderInfo::StrictImplicit => ("strictImplicitBinder", "⦃", "⦄"),
        BinderInfo::InstImplicit => unreachable!("handled above"),
    };
    let mut args = vec![
        atom(open),
        null(vec![name]),
        null(type_.map_or_else(Vec::new, |type_| vec![atom(":"), type_.clone()])),
    ];
    if style == BinderInfo::Default {
        args.push(null(vec![]));
    }
    args.push(atom(close));
    Syntax::node(parser_kind(&["Term", kind]), args)
}

impl Context {
    /// `replaceBinderAnnotation` (vendored Lean/Elab/BuiltinCommand.lean): only
    /// typeless binders update existing variables, and the latest declaration
    /// of a name wins. Unmatched names remain ordinary new binders. Process all
    /// updates before declaring that residue, as the pin's `flatMapM` does.
    fn section_binder_updates(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut variables = self.source_scope.variables.clone();
        let mut locals = self.txn.lctx.decls().to_vec();
        let mut residue = Vec::new();
        for incoming in expect_null_args(syntax, "declaration binders")? {
            self.tick()?;
            let binder = variable_binder(incoming)?;
            let mut names = if binder.style == BinderInfo::InstImplicit
                && binder.names.is_empty()
                && let Some(name @ Syntax::Ident { .. }) = binder.type_
            {
                vec![name.clone()]
            } else if binder.type_.is_none() && !binder.has_default {
                binder.names.to_vec()
            } else {
                residue.push(incoming.clone());
                continue;
            };
            let initial = names.len();
            // Locate the same written occurrence in syntax and in the checked
            // local context. Consume even unselected occurrences so shadowed
            // names never change an older variable's identity or dependencies.
            let mut positions: HashMap<Name, Vec<usize>> = HashMap::new();
            for (index, local) in locals.iter().enumerate() {
                self.tick()?;
                positions
                    .entry(local.user_name.clone())
                    .or_default()
                    .push(index);
            }
            for (command, _) in variables.commands.iter_mut().rev() {
                let mut groups = expect_null_args(command, "stored variable binders")?.to_vec();
                for group_index in (0..groups.len()).rev() {
                    self.tick()?;
                    let old = variable_binder(&groups[group_index])?;
                    let mut replacements = Vec::new();
                    let mut changed = false;
                    for name in old.names.iter().rev() {
                        self.tick()?;
                        let Syntax::Ident { val, .. } = name else {
                            replacements.push(rebuilt_binder(name.clone(), old.type_, old.style));
                            continue;
                        };
                        let position = positions.get_mut(val).and_then(Vec::pop);
                        let selected = names.iter().position(|candidate| {
                            matches!(candidate, Syntax::Ident { val: target, .. } if target == val)
                        });
                        let style = if let Some(selected) = selected {
                            if old.has_default {
                                return Err(error(ScopeError::VariableBinderUpdateWithDefault));
                            }
                            if old.style == binder.style {
                                return Err(error(ScopeError::RedundantVariableBinderUpdate));
                            }
                            let position =
                                position.ok_or_else(|| failure(SourceInferenceError::Scope))?;
                            if binder.style == BinderInfo::InstImplicit {
                                if old.type_.is_none() {
                                    return Err(error(
                                        ScopeError::InstanceBinderUpdateWithoutType(val.clone()),
                                    ));
                                }
                                self.validate_instance_binder(&locals[position].type_)?;
                            }
                            names.remove(selected);
                            locals[position].binder_info = binder.style;
                            changed = true;
                            binder.style
                        } else {
                            old.style
                        };
                        replacements.push(rebuilt_binder(name.clone(), old.type_, style));
                    }
                    if changed {
                        replacements.reverse();
                        groups.splice(group_index..=group_index, replacements);
                    }
                }
                *command = Syntax::node(Name::from_components(["null"]), groups);
            }
            if names.len() == initial {
                residue.push(incoming.clone());
            } else {
                if binder.style == BinderInfo::InstImplicit && !names.is_empty() {
                    return Err(failure(SourceInferenceError::Scope));
                }
                residue.extend(
                    names
                        .into_iter()
                        .map(|name| rebuilt_binder(name, None, binder.style)),
                );
            }
        }
        let mut lctx = LocalContext::new();
        for local in locals {
            lctx.add_param(local.id, local.user_name, local.type_, local.binder_info);
        }
        self.txn.lctx = lctx.clone();
        variables.locals = lctx;
        self.source_scope.variables = variables;
        Ok(Syntax::node(Name::from_components(["null"]), residue))
    }
}

/// Return a successor only after the entire telescope is elaborated, all holes
/// are resolved, and its closed type passes the ordinary kernel. This check
/// publishes no axiom or other declaration, even for unused section variables.
pub fn declare(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
) -> Result<SectionVariables, NatDefinitionElabError> {
    elaborate_command(syntax, env, kernel, scope, true)
}

/// [`declare`]'s elaboration. Without `kernel_check` the closed telescope is not checked again:
/// a declaration elaborates the commands again only to compare each local with the one
/// [`declare`] checked, and refuses on any difference. Fresh names are drawn exactly as
/// [`declare`] draws them, so equal elaborations yield equal locals.
fn elaborate_command(
    syntax: &Syntax,
    env: &Environment,
    kernel: Budget,
    scope: &SourceScope,
    kernel_check: bool,
) -> Result<SectionVariables, NatDefinitionElabError> {
    let mut context = Context::scoped(env, kernel, scope);
    context.declare_levels(&Syntax::node(Name::from_components(["null"]), vec![]))?;
    context.infer_level_params = true;
    let syntax = if kernel_check {
        context.section_binder_updates(syntax)?
    } else {
        // Stored commands already contain only declaration residue, with the
        // latest annotations substituted at their original binder positions.
        syntax.clone()
    };
    // Auto-bound implicits become implicit variables of their own, included where used, as at the
    // pin (`@r : ∀ {α : Sort u_1} (R : α → α → Prop) (x : α), …` after `variable (R : α → α → Prop)`).
    let (autos, written) =
        context.with_auto_bound_implicits(&[], |context| context.bind_parameters(&syntax))?;
    context.refuse_auto_bound_dependencies(&autos, &written)?;
    if context.txn.lctx.len() > MAX_SECTION_VARIABLES {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let mut locals = context.txn.lctx.decls().to_vec();
    let types: Vec<_> = locals.iter().map(|local| local.type_.clone()).collect();
    context.generalize_declaration_universes(&types)?;
    for local in &mut locals {
        local.type_ = context.instantiate(&local.type_)?;
        context.require_resolved(std::slice::from_ref(&local.type_))?;
    }
    let mut closed = Expr::sort(Level::zero());
    for local in locals.iter().rev() {
        context.tick()?;
        closed = closed
            .abstract_fvar(&local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        closed = Expr::forall_e(
            local.user_name.clone(),
            local.type_.clone(),
            closed,
            local.binder_info,
        );
    }
    let name = loop {
        let name = context.fresh_name()?;
        if !env.contains(&name) {
            break name;
        }
    };
    let declaration = Declaration::Axiom(fln_env::constants::AxiomVal {
        base: ConstantVal {
            name,
            level_params: context.declaration_levels(std::slice::from_ref(&closed))?,
            type_: closed,
        },
        is_unsafe: false,
    });
    if kernel_check {
        match check(env, &declaration, kernel) {
            Outcome::Complete(Verdict::Accepted { .. }) => {}
            outcome => {
                return Err(failure(SourceInferenceError::TypeObligation(Box::new(
                    outcome,
                ))));
            }
        }
    }
    let mut lctx = LocalContext::new();
    for local in locals {
        lctx.add_param(local.id, local.user_name, local.type_, local.binder_info);
    }
    let mut commands = context.source_scope.variables.commands.clone();
    // Even an update-only command consumes the temporary telescope-check name
    // above. Replay its empty residue too, so later variables keep their IDs.
    commands.push((syntax, lctx.len()));
    Ok(SectionVariables {
        locals: lctx,
        next: context.next,
        levels: context.level_params,
        included: scope.variables.included.clone(),
        omitted: scope.variables.omitted.clone(),
        commands,
    })
}

impl Context {
    /// Metered DAG traversal, including annotation and let domains. This must
    /// inspect instantiated terms so dictionary/unification assignments cannot
    /// hide a dependency from generalization or theorem-header filtering.
    fn section_dependencies(
        &mut self,
        roots: &[Expr],
    ) -> Result<HashSet<FVarId>, NatDefinitionElabError> {
        let mut pending = Vec::new();
        for root in roots {
            pending.push(self.instantiate(root)?);
        }
        let mut seen = HashSet::new();
        let mut used = HashSet::new();
        while let Some(expr) = pending.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::FVar { id } => {
                    used.insert(id.clone());
                }
                ExprNode::App { f, a } => pending.extend([f.clone(), a.clone()]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    pending.extend([binder_type.clone(), body.clone()]);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => pending.extend([type_.clone(), value.clone(), body.clone()]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    pending.push(expr.clone())
                }
                _ => {}
            }
        }
        Ok(used)
    }

    /// Dependencies close in reverse declaration order; instance parameters are
    /// then included only when every variable in their type is already included.
    /// The theorem caller runs this before elaborating the proof and removes all
    /// other section locals, so a proof cannot silently strengthen its statement.
    pub(in crate::source) fn section_parameters(
        &mut self,
        roots: &[Expr],
        include_instances: bool,
    ) -> Result<Vec<LocalDecl>, NatDefinitionElabError> {
        let locals = self.source_scope.variables.locals.decls().to_vec();
        let mut used = self.section_dependencies(roots)?;
        if include_instances {
            used.extend(self.source_scope.variables.included.iter().cloned());
        }
        for local in locals.iter().rev() {
            self.tick()?;
            if used.contains(&local.id) {
                used.extend(self.section_dependencies(std::slice::from_ref(&local.type_))?);
            }
        }
        if include_instances {
            // Omitting a signature dependency is an error, not permission to
            // alter the theorem's type or to leave a dangling free variable.
            for local in &locals {
                self.tick()?;
                if used.contains(&local.id)
                    && self.source_scope.variables.omitted.contains(&local.id)
                {
                    return Err(error(ScopeError::OmittedVariable(local.user_name.clone())));
                }
            }
            for local in &locals {
                self.tick()?;
                if local.binder_info == BinderInfo::InstImplicit
                    && !self.source_scope.variables.omitted.contains(&local.id)
                    && self
                        .section_dependencies(std::slice::from_ref(&local.type_))?
                        .iter()
                        .all(|id| used.contains(id))
                {
                    used.insert(local.id.clone());
                }
            }
        }
        let selected: Vec<LocalDecl> = locals
            .into_iter()
            .filter(|local| used.contains(&local.id))
            .collect();
        if !selected.is_empty() {
            let selected_ids: HashSet<&FVarId> = selected.iter().map(|local| &local.id).collect();
            let through = self
                .source_scope
                .variables
                .locals
                .decls()
                .iter()
                .rposition(|local| selected_ids.contains(&local.id))
                .map_or(0, |position| position + 1);
            let changed = self.reinterpreted_section_variables(through)?;
            if let Some(local) = selected.iter().find(|local| changed.contains(&local.id)) {
                return Err(error(ScopeError::ReinterpretedVariable(
                    local.user_name.clone(),
                )));
            }
        }
        if let Some(group) = self.partial.as_mut().and_then(|state| state.group.as_mut()) {
            group.captures = selected.clone();
        }
        Ok(selected)
    }

    /// The section variables whose binders elaborate differently in this declaration's scope
    /// and environment than they did at their `variable` commands. The pin elaborates the
    /// commands' syntax again in every declaration (`Lean.Elab.Command.runTermElabM` over
    /// `varDecls`), so after `open Second` an earlier `Carrier` may name `Second.Carrier`, or
    /// be ambiguous. The commands are elaborated again here, in order, and each local compared
    /// with the one first checked; a command that no longer elaborates leaves its locals and
    /// every later one unconfirmed. Only the first `through` locals are confirmed: a command
    /// never depends on a later one, so the commands after the one completing them are not read.
    fn reinterpreted_section_variables(
        &mut self,
        through: usize,
    ) -> Result<HashSet<FVarId>, NatDefinitionElabError> {
        let stored = self.source_scope.variables.clone();
        let mut scope = self.source_scope.clone();
        scope.variables = SectionVariables::default();
        for (syntax, after) in &stored.commands {
            self.tick()?;
            if scope.variables.locals.len() >= through {
                break;
            }
            if let Ok(variables) =
                elaborate_command(syntax, &self.txn.env, self.kernel, &scope, false)
            {
                scope.variables = variables;
                if *after >= through {
                    break;
                }
                continue;
            }
            // The pin elaborates binders one group at a time: a later group that no longer
            // elaborates leaves the earlier ones as they are. Keep the longest prefix that does.
            if let Syntax::Node { kind, args, .. } = syntax {
                for end in (1..args.len()).rev() {
                    self.tick()?;
                    let prefix = Syntax::node(kind.clone(), args[..end].to_vec());
                    if let Ok(variables) =
                        elaborate_command(&prefix, &self.txn.env, self.kernel, &scope, false)
                    {
                        scope.variables = variables;
                        break;
                    }
                }
            }
            break;
        }
        let renewed = scope.variables.locals.decls();
        let mut changed = HashSet::new();
        for (position, local) in stored.locals.decls().iter().enumerate().take(through) {
            self.tick()?;
            let same = renewed.get(position).is_some_and(|again| {
                again.id == local.id
                    && again.user_name == local.user_name
                    && again.type_ == local.type_
                    && again.binder_info == local.binder_info
            });
            if !same {
                changed.insert(local.id.clone());
            }
        }
        Ok(changed)
    }

    pub(in crate::source) fn restrict_section_locals(&mut self, selected: &[LocalDecl]) {
        let all: HashSet<_> = self
            .source_scope
            .variables
            .locals
            .decls()
            .iter()
            .map(|local| &local.id)
            .collect();
        let keep: HashSet<_> = selected.iter().map(|local| &local.id).collect();
        let mut lctx = LocalContext::new();
        for local in self.txn.lctx.decls() {
            if !all.contains(&local.id) || keep.contains(&local.id) {
                lctx.add_param(
                    local.id.clone(),
                    local.user_name.clone(),
                    local.type_.clone(),
                    local.binder_info,
                );
            }
        }
        self.txn.lctx = lctx;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selection_is_atomic_bounded_and_idempotent() {
        let name = Name::from_components(["h"]);
        let id = FVarId(Name::from_components(["section", "h"]));
        let mut vars = SectionVariables::default();
        vars.locals.add_param(
            id.clone(),
            name.clone(),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        );
        vars.select(std::slice::from_ref(&name), true).unwrap();
        let before = vars.clone();
        assert!(
            vars.select(&[name.clone(), Name::from_components(["missing"])], false)
                .is_err()
        );
        assert_eq!(vars, before);
        assert!(
            vars.select(&vec![name.clone(); MAX_SECTION_VARIABLES + 1], false)
                .is_err()
        );
        assert_eq!(vars, before);
        vars.select(&[name.clone(), name.clone()], true).unwrap();
        assert_eq!(vars, before);
        vars.select(std::slice::from_ref(&name), false).unwrap();
        assert!(vars.omitted.contains(&id));
        assert!(vars.included.is_empty());
        vars.select(&[name], true).unwrap();
        assert_eq!(vars, before);
    }

    #[test]
    fn include_selects_the_first_occurrence_and_omit_selects_all_occurrences() {
        let name = Name::from_components(["h"]);
        let first = FVarId(Name::from_components(["section", "first"]));
        let last = FVarId(Name::from_components(["section", "last"]));
        let mut vars = SectionVariables::default();
        for id in [&first, &last] {
            vars.locals.add_param(
                id.clone(),
                name.clone(),
                Expr::sort(Level::zero()),
                BinderInfo::Default,
            );
        }
        vars.select(std::slice::from_ref(&name), true).unwrap();
        assert_eq!(vars.included, HashSet::from([first.clone()]));
        vars.select(std::slice::from_ref(&name), false).unwrap();
        assert_eq!(vars.omitted, HashSet::from([first.clone(), last.clone()]));
        assert!(vars.included.is_empty());
        vars.select(&[name], true).unwrap();
        assert_eq!(vars.included, HashSet::from([first]));
        assert_eq!(vars.omitted, HashSet::from([last]));
    }
}
