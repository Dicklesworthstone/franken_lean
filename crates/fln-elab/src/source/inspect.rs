//! Read-only observations from the real native term and tactic drivers.
//!
//! Inspection stops before the selected tactic, or after the selected term.
//! An unfinished proof is never manufactured into a declaration. The private
//! stop is non-recoverable by `try`/`first`, and ordinary admission has no probe.
use super::*;
use std::ops::Range;

/// The discrimination-tree filter's read-only audit (bead `fln-52qv`).
pub use super::instances::audit::{
    CandidateAudit, Choice, InstanceGoalAudit, Selection, audit_instance_goal,
};

/// Which elaboration boundary the caller wants to observe.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObservationKind {
    Goals,
    Term,
    /// The actual local context before an identifier is resolved. The selected
    /// identifier may be incomplete; no term or declaration is manufactured.
    Completion,
    /// A term's type in its actual local context, including the inferred-type
    /// fallback used by the pin's plainTermGoal. The observation is `Goals`
    /// with one provisional goal, never a declaration-admission certificate.
    TermGoal,
}

/// A live obligation, not an accepted proof. Types and locals are instantiated
/// through the same metavariable store used by the native tactic driver.
#[derive(Debug, Clone)]
pub struct ObservedGoal {
    /// Existing tactic obligation; inferred term types do not invent a metavariable.
    pub id: Option<MVarId>,
    pub user_name: Option<Name>,
    pub target: Expr,
    pub locals: LocalContext,
    // The world actually used at the observation point. Public headers and
    // private bodies may have different environments in the same declaration.
    environment: Environment,
}

impl ObservedGoal {
    /// Construct an inspector in this observation's actual native world, not
    /// the caller's later environment or the module's private prefix.
    pub fn expression_inspector(
        &self,
        kernel: Budget,
        max_heartbeats: u64,
    ) -> Result<ExpressionInspector, NatDefinitionElabError> {
        ExpressionInspector::new(&self.environment, &self.locals, kernel, max_heartbeats)
    }
}

/// Read-only type reconstruction for expressions already observed by the native
/// elaborator. The private transaction never publishes assignments or admits a
/// declaration. In particular, a reconstructed type is presentation metadata,
/// not a kernel verdict. Unassigned metavariables may have no recoverable type.
pub struct ExpressionInspector {
    context: Context,
    types: std::collections::HashMap<Expr, Option<Expr>>,
}

impl ExpressionInspector {
    /// All queries share one heartbeat budget and a bounded cache. Zero is a
    /// refusal, not the elaborator's convention for an unlimited budget.
    pub fn new(
        environment: &Environment,
        locals: &LocalContext,
        kernel: Budget,
        max_heartbeats: u64,
    ) -> Result<Self, NatDefinitionElabError> {
        if max_heartbeats == 0 || locals.len() > 4096 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut context = Context::new(environment, kernel);
        context.txn.budget.max_heartbeats = max_heartbeats;
        context.txn.lctx = locals.clone();
        // Type reconstruction opens binders using the source driver's name
        // generator. Its temporaries must not capture an observed free variable.
        let generated = Name::from_components(["_fln_source"]);
        for local in locals.decls() {
            context.tick()?;
            if local.id.0.parent() == generated
                && let fln_core::name::LeafView::Num(index) = local.id.0.leaf_view()
            {
                context.next = context.next.max(
                    index
                        .checked_add(1)
                        .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?,
                );
            }
        }
        Ok(Self {
            context,
            types: std::collections::HashMap::new(),
        })
    }

    /// Reuse the same native reconstruction used by source constraints, including
    /// universe instantiation and dependent application/projection types. Loose
    /// bound variables require an enclosing binder and are not guessed here.
    pub fn type_of(&mut self, expression: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.context.tick()?;
        if expression.has_loose_bvars() {
            return Ok(None);
        }
        if let Some(type_) = self.types.get(expression) {
            return Ok(type_.clone());
        }
        if self.types.len() >= 4096 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let type_ = self.context.known_type(expression)?;
        self.types.insert(expression.clone(), type_.clone());
        Ok(type_)
    }
}

#[derive(Debug, Clone)]
pub enum SourceObservation {
    Goals {
        range: Range<usize>,
        goals: Vec<ObservedGoal>,
    },
    Term {
        range: Range<usize>,
        expression: Expr,
        type_: Expr,
        locals: LocalContext,
    },
    Completion {
        range: Range<usize>,
        locals: LocalContext,
    },
}
impl SourceObservation {
    pub fn range(&self) -> Range<usize> {
        match self {
            Self::Goals { range, .. }
            | Self::Term { range, .. }
            | Self::Completion { range, .. } => range.clone(),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
enum Site {
    Tactic(Range<usize>),
    By(Range<usize>),
    End(Range<usize>),
    Term(Range<usize>),
    Completion(Range<usize>),
    TermGoal {
        range: Range<usize>,
        /// None identifies an identifier; nodes retain their exact parser kind.
        kind: Option<Name>,
    },
}
impl Site {
    fn range(&self) -> &Range<usize> {
        match self {
            Self::Tactic(r) | Self::By(r) | Self::End(r) | Self::Term(r) | Self::Completion(r) => r,
            Self::TermGoal { range, .. } => range,
        }
    }
}
#[derive(Clone)]
pub(super) struct Probe {
    site: Site,
    result: Option<SourceObservation>,
}

/// An original identifier resolved by the ordinary elaborator, before implicit
/// arguments are inserted. Local variables are deliberately absent: the pinned
/// frontend writes `.ilean` with `findModuleRefs (localVars := false)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceReference {
    pub name: Name,
    pub range: Range<usize>,
}

/// Term speculation clones and restores this log with elaborator state. Tactic
/// alternatives retain it across their semantic rollback, matching the pin's
/// `restoreInfo := false`: even a failed proof branch has editor references.
#[derive(Clone)]
pub(super) struct ReferenceCollector {
    references: Vec<SourceReference>,
    complete: bool,
    limit: usize,
}

/// Reconstruct references in an already checked declaration using its exact
/// prefix world. This returns metadata only, never an admission token. `None`
/// means a field/projection reference needs source information not yet retained
/// by this collector; callers must refuse the artifact rather than omit it.
pub fn declaration_references(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
    max_references: usize,
) -> Result<Option<Vec<SourceReference>>, NatDefinitionElabError> {
    let scope = scope.for_declaration(syntax)?;
    let mut context = Context::scoped(environment, kernel, &scope)?;
    collect_references(syntax, &mut context, max_references)
}

/// Preserve admission's exported-header/private-body transition for public
/// theorems, instances and definitions whose implementation is hidden.
pub fn public_declaration_references(
    syntax: &Syntax,
    worlds: &TheoremWorlds<'_>,
    kernel: Budget,
    max_references: usize,
) -> Result<Option<Vec<SourceReference>>, NatDefinitionElabError> {
    let mut context = if is_theorem(syntax) {
        Context::public_theorem(syntax, worlds, kernel)?
    } else if is_instance(syntax) {
        Context::public_instance(syntax, worlds, kernel)?
    } else {
        Context::public_definition(syntax, worlds, kernel)?
    };
    collect_references(syntax, &mut context, max_references)
}

fn collect_references(
    syntax: &Syntax,
    context: &mut Context,
    max_references: usize,
) -> Result<Option<Vec<SourceReference>>, NatDefinitionElabError> {
    context.references = Some(ReferenceCollector {
        references: Vec::new(),
        complete: true,
        limit: max_references,
    });
    definition_in_context(syntax, context)?;
    let collected = context
        .references
        .take()
        .expect("reference collection enabled");
    Ok(collected.complete.then_some(collected.references))
}

impl Context {
    pub(super) fn refuse_reference_metadata(&mut self) {
        if let Some(collector) = &mut self.references {
            collector.complete = false;
        }
    }

    pub(super) fn record_reference(
        &mut self,
        syntax: &Syntax,
        term: &Typed,
    ) -> Result<(), NatDefinitionElabError> {
        let Some(collector) = &mut self.references else {
            return Ok(());
        };
        let identifier = match syntax {
            Syntax::Ident { .. } => syntax,
            Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Term", "explicitUniv"]) => {
                let Some(identifier @ Syntax::Ident { .. }) = args.first() else {
                    collector.complete = false;
                    return Ok(());
                };
                identifier
            }
            _ => return Ok(()),
        };
        let fln_syntax::source::SourceInfo::Original { pos, end_pos, .. } = identifier.info()
        else {
            return Ok(());
        };
        let name = match term.value.node() {
            ExprNode::Const { name, .. } => name,
            ExprNode::FVar { .. } => return Ok(()),
            // A qualified field identifier is an application/projection, whose
            // field-only source span must not be guessed from its spelling.
            _ => {
                collector.complete = false;
                return Ok(());
            }
        };
        if collector.references.len() >= collector.limit {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        collector.references.push(SourceReference {
            name: name.clone(),
            range: pos.0..end_pos.0,
        });
        Ok(())
    }
}

/// Observe one parsed native declaration at a UTF-8 byte position in the syntax's coordinate system.
/// The caller supplies its checked prefix environment and lexical name scope.
/// No candidate, environment successor, or admission token is returned.
/// Unknown syntax and failures before the selected boundary remain errors.
pub fn declaration(
    syntax: &Syntax,
    environment: &Environment,
    kernel: Budget,
    scope: &SourceScope,
    offset: usize,
    kind: ObservationKind,
) -> Result<Option<SourceObservation>, NatDefinitionElabError> {
    let scope = scope.for_declaration(syntax)?;
    let mut context = Context::scoped(environment, kernel, &scope)?;
    declaration_in_context(syntax, &mut context, offset, kind)
}

/// Observe a module's public theorem with its exported header and private proof
/// in the same worlds used by ordinary elaboration. A proof observation cannot
/// change or rescue an incomplete exported signature.
pub fn public_theorem(
    syntax: &Syntax,
    worlds: &TheoremWorlds<'_>,
    kernel: Budget,
    offset: usize,
    kind: ObservationKind,
) -> Result<Option<SourceObservation>, NatDefinitionElabError> {
    let mut context = Context::public_theorem(syntax, worlds, kernel)?;
    declaration_in_context(syntax, &mut context, offset, kind)
}

/// A provisional observation and the world actually entered at its position.
/// Header observations never select the hidden implementation's instance scope.
#[derive(Debug)]
pub struct PublicInstanceObservation {
    pub observation: Option<SourceObservation>,
    pub private_body: bool,
}

pub fn public_instance(
    syntax: &Syntax,
    worlds: &TheoremWorlds<'_>,
    kernel: Budget,
    offset: usize,
    kind: ObservationKind,
) -> Result<PublicInstanceObservation, NatDefinitionElabError> {
    let mut context = Context::public_instance(syntax, worlds, kernel)?;
    let observation = declaration_in_context(syntax, &mut context, offset, kind)?;
    Ok(PublicInstanceObservation {
        observation,
        private_body: context.private_instance_body,
    })
}

/// Observe a hidden definition using exactly the same public-header/private-
/// implementation transition as admission. The flag is set only when that
/// transition actually occurred, never by the cursor's spelling or position.
pub fn public_definition(
    syntax: &Syntax,
    worlds: &TheoremWorlds<'_>,
    kernel: Budget,
    offset: usize,
    kind: ObservationKind,
) -> Result<PublicInstanceObservation, NatDefinitionElabError> {
    let mut context = Context::public_definition(syntax, worlds, kernel)?;
    let observation = declaration_in_context(syntax, &mut context, offset, kind)?;
    Ok(PublicInstanceObservation {
        observation,
        private_body: context.public_definition_header.is_some(),
    })
}

fn declaration_in_context(
    syntax: &Syntax,
    context: &mut Context,
    offset: usize,
    kind: ObservationKind,
) -> Result<Option<SourceObservation>, NatDefinitionElabError> {
    // There will be no final declaration admission to discharge earlier rigid
    // equations. Check them when generated instead of deferring to that door.
    context.attempt_depth = 1;
    let Some(site) = select(context, syntax, offset, kind)? else {
        return Ok(None);
    };
    context.inspection = Some(Probe { site, result: None });
    match definition_in_context(syntax, context) {
        Err(NatDefinitionElabError::Inference(SourceInferenceError::ObservationComplete)) => {
            Ok(context.inspection.take().and_then(|probe| probe.result))
        }
        Ok(_) => Ok(None),
        Err(error) => Err(error),
    }
}

/// One postorder pass, rather than rescanning every subtree to find its span.
fn select(
    context: &mut Context,
    syntax: &Syntax,
    offset: usize,
    wanted: ObservationKind,
) -> Result<Option<Site>, NatDefinitionElabError> {
    let mut spans = std::collections::HashMap::new();
    let mut stack = vec![(syntax, false)];
    let mut sites = Vec::new();
    let mut blocks = Vec::new();
    while let Some((node, exiting)) = stack.pop() {
        context.tick()?;
        if !exiting {
            stack.push((node, true));
            if let Syntax::Node { args, .. } = node {
                stack.extend(args.iter().rev().map(|child| (child, false)));
            }
            continue;
        }
        let span = match node {
            Syntax::Node { args, .. } => {
                let mut bounds: Option<Range<usize>> = None;
                for child in args {
                    if let Some(Some(r)) = spans.get(&std::ptr::from_ref(child)) {
                        let r: &Range<usize> = r;
                        bounds = Some(match bounds {
                            None => r.clone(),
                            Some(old) => old.start.min(r.start)..old.end.max(r.end),
                        });
                    }
                }
                bounds
            }
            _ => node
                .info()
                .pos(true)
                .zip(node.info().end_pos(true))
                .map(|(a, b)| a.0..b.0),
        };
        spans.insert(std::ptr::from_ref(node), span.clone());
        let Some(r) = span else { continue };
        if wanted == ObservationKind::TermGoal {
            match node {
                Syntax::Ident { .. } => sites.push(Site::TermGoal {
                    range: r,
                    kind: None,
                }),
                // Literals are `numLitKind`, `scientificLitKind`, `strLitKind`, `charLitKind`
                // and `nameLitKind` nodes, not `Term.*` ones, yet the pin's literal elaborators
                // record term info for them, so plainTermGoal answers at a literal too.
                Syntax::Node { kind, .. }
                    if kind.parent() == parser_kind(&["Term"])
                        || (kind.parent() == Name::anonymous()
                            && matches!(
                                kind.to_display_string().as_str(),
                                "num" | "scientific" | "str" | "char" | "name"
                            )) =>
                {
                    sites.push(Site::TermGoal {
                        range: r,
                        kind: Some(kind.clone()),
                    });
                }
                _ => {}
            }
        } else if matches!(wanted, ObservationKind::Term | ObservationKind::Completion)
            && matches!(node, Syntax::Ident { .. })
        {
            sites.push(if wanted == ObservationKind::Completion {
                Site::Completion(r)
            } else {
                Site::Term(r)
            });
        } else if wanted == ObservationKind::Goals
            && let Syntax::Node { kind, args, .. } = node
        {
            if kind == &parser_kind(&["Term", "byTactic"])
                || kind == &parser_kind(&["Term", "byTactic'"])
            {
                blocks.push(r.clone());
                if let Some(keyword) = args.first()
                    && let Some((a, b)) = keyword.info().pos(true).zip(keyword.info().end_pos(true))
                {
                    sites.push(Site::By(a.0..b.0));
                }
            } else if (kind.parent() == parser_kind(&["Tactic"])
                || kind == &Name::from_components(["Lean", "cdot"]))
                && ![
                    "tacticSeq",
                    "tacticSeq1Indented",
                    "paren",
                    "rwRule",
                    "rwRuleSeq",
                    "location",
                    "locationHyp",
                    "locationType",
                    "locationWildcard",
                ]
                .iter()
                .any(|name| kind == &parser_kind(&["Tactic", name]))
            {
                sites.push(Site::Tactic(r));
            }
        }
    }
    if let Some(site) = sites
        .iter()
        .filter(|site| site.range().contains(&offset))
        .min_by_key(|site| site.range().len())
    {
        return Ok(Some(site.clone()));
    }
    if wanted == ObservationKind::Goals {
        if let Some(block) = blocks
            .iter()
            .filter(|r| r.contains(&offset))
            .min_by_key(|r| r.len())
        {
            return Ok(sites
                .iter()
                .filter(|site| {
                    matches!(site, Site::Tactic(_))
                        && site.range().start >= offset
                        && site.range().end <= block.end
                })
                .min_by_key(|site| (site.range().start, site.range().len()))
                .cloned());
        }
        let end = spans
            .get(&std::ptr::from_ref(syntax))
            .and_then(|r| r.as_ref())
            .map(|r| r.end);
        if end.is_some_and(|end| offset >= end) {
            return Ok(blocks
                .into_iter()
                .filter(|r| Some(r.end) == end)
                .max_by_key(|r| r.len())
                .map(Site::End));
        }
    }
    Ok(None)
}

impl Context {
    /// Stop on the ordinary term driver's local scope, before looking up the
    /// partial name. Earlier type errors and resource stops still propagate.
    pub(super) fn observe_completion(
        &mut self,
        syntax: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let Some(Probe {
            site: Site::Completion(range),
            ..
        }) = &self.inspection
        else {
            return Ok(());
        };
        if !matches!(syntax, Syntax::Ident { .. })
            || syntax.info().pos(true).is_none_or(|p| p.0 != range.start)
            || syntax.info().end_pos(true).is_none_or(|p| p.0 != range.end)
        {
            return Ok(());
        }
        self.flush(true)?;
        let locals = self.observation_locals(&self.txn.lctx.clone(), &[])?;
        let probe = self.inspection.as_mut().expect("selected completion probe");
        probe.result = Some(SourceObservation::Completion {
            range: probe.site.range().clone(),
            locals,
        });
        Err(failure(SourceInferenceError::ObservationComplete))
    }

    pub(super) fn observation_extent(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Range<usize>>, NatDefinitionElabError> {
        if self.inspection.is_none() {
            return Ok(None);
        }
        let mut range: Option<Range<usize>> = None;
        let mut stack = vec![syntax];
        while let Some(node) = stack.pop() {
            self.tick()?;
            if let Syntax::Node { args, .. } = node {
                stack.extend(args);
            } else if let Some((a, b)) = node.info().pos(true).zip(node.info().end_pos(true)) {
                range = Some(match range {
                    None => a.0..b.0,
                    Some(r) => r.start.min(a.0)..r.end.max(b.0),
                });
            }
        }
        Ok(range)
    }
    fn observation_locals(
        &mut self,
        source: &LocalContext,
        roots: &[&Expr],
    ) -> Result<LocalContext, NatDefinitionElabError> {
        let mut needed = std::collections::HashSet::new();
        for root in roots {
            needed.extend(self.elimination_reads(root)?);
        }
        let mut retained = Vec::new();
        // The predefinition's auxiliary self is not a user hypothesis. Keep it
        // only when the observed term/goal or a visible local actually uses it.
        // Local declarations depend on earlier ones, so reverse traversal also
        // closes dependencies through retained local types and let values.
        for local in source.decls().iter().rev() {
            self.tick()?;
            let private_self = self.is_private_self(&local.id)
                || self
                    .partial
                    .as_ref()
                    .and_then(|partial| partial.reference.as_ref())
                    .is_some_and(|reference| {
                        matches!(reference.term.value.node(), ExprNode::FVar { id } if id == &local.id)
                    });
            if private_self && !needed.contains(&local.id) {
                continue;
            }
            let mut local = local.clone();
            local.type_ = self.instantiate(&local.type_)?;
            local.value = local
                .value
                .as_ref()
                .map(|value| self.instantiate(value))
                .transpose()?;
            needed.extend(self.elimination_reads(&local.type_)?);
            if let Some(value) = &local.value {
                needed.extend(self.elimination_reads(value)?);
            }
            retained.push(local);
        }
        let mut result = LocalContext::new();
        for local in retained.into_iter().rev() {
            self.tick()?;
            if let Some(value) = local.value {
                result.add_let(local.id, local.user_name, local.type_, value);
            } else {
                result.add_param(local.id, local.user_name, local.type_, local.binder_info);
            }
        }
        Ok(result)
    }
    pub(super) fn observes_term(&self, syntax: &Syntax) -> bool {
        let Some(probe) = &self.inspection else {
            return false;
        };
        match &probe.site {
            Site::Term(range) => {
                matches!(syntax, Syntax::Ident { .. })
                    && syntax.info().pos(true).is_some_and(|p| p.0 == range.start)
                    && syntax
                        .info()
                        .end_pos(true)
                        .is_some_and(|p| p.0 == range.end)
            }
            // The driver schedules the existing post-term observation task.
            // Exact spans are checked there with the charged traversal below;
            // this inexpensive prefilter adds no unbudgeted subtree walk.
            Site::TermGoal { kind, .. } => match (kind, syntax) {
                (None, Syntax::Ident { .. }) => true,
                (Some(selected), Syntax::Node { kind, .. }) => selected == kind,
                _ => false,
            },
            _ => false,
        }
    }
    pub(super) fn observe_term(
        &mut self,
        syntax: &Syntax,
        term: Typed,
        locals: LocalContext,
    ) -> Result<(), NatDefinitionElabError> {
        if !self.observes_term(syntax) {
            return Ok(());
        }
        if let Some(Probe {
            site: Site::TermGoal { range, .. },
            ..
        }) = &self.inspection
        {
            let selected = range.clone();
            if self.observation_extent(syntax)?.as_ref() != Some(&selected) {
                return Ok(());
            }
            // Expected-typed holes already carry their actual domain; an
            // inference-only term carries its inferred type. Observe before
            // declaration finalization, which would refuse unfinished holes.
            // An invalid selected term still fails rather than inventing info.
            self.flush(true)?;
            let target = self.instantiate(&term.type_)?;
            let locals = self.observation_locals(&locals, &[&target])?;
            let environment = self.txn.env.clone();
            let probe = self.inspection.as_mut().expect("selected term-goal probe");
            probe.result = Some(SourceObservation::Goals {
                range: probe.site.range().clone(),
                goals: vec![ObservedGoal {
                    id: None,
                    user_name: None,
                    target,
                    locals,
                    environment,
                }],
            });
            return Err(failure(SourceInferenceError::ObservationComplete));
        }
        self.flush(true)?;
        let expression = self.instantiate(&term.value)?;
        let type_ = self.instantiate(&term.type_)?;
        let locals = self.observation_locals(&locals, &[&expression, &type_])?;
        let probe = self.inspection.as_mut().expect("selected probe");
        probe.result = Some(SourceObservation::Term {
            range: probe.site.range().clone(),
            expression,
            type_,
            locals,
        });
        Err(failure(SourceInferenceError::ObservationComplete))
    }
    pub(super) fn observe_by(
        &mut self,
        keyword: &Syntax,
        goal: &tactics::ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        let selected = self.inspection.as_ref().is_some_and(|probe| {
            let range = match &probe.site {
                Site::By(range) => range,
                Site::TermGoal {
                    range,
                    kind: Some(kind),
                } if kind == &parser_kind(&["Term", "byTactic"])
                    || kind == &parser_kind(&["Term", "byTactic'"]) =>
                {
                    range
                }
                _ => return false,
            };
            keyword.info().pos(true).is_some_and(|p| p.0 == range.start)
        });
        if selected {
            // The by-term's expected goal exists before its first tactic runs.
            return self.observe_goals(std::slice::from_ref(goal));
        }
        Ok(())
    }
    pub(super) fn observes_goal(
        &mut self,
        instruction: Option<&Syntax>,
        extent: Option<&Range<usize>>,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(probe) = &self.inspection else {
            return Ok(false);
        };
        let site = probe.site.clone();
        match (site, instruction) {
            (Site::Tactic(range), Some(instruction)) => {
                Ok(self.observation_extent(instruction)?.as_ref() == Some(&range))
            }
            (Site::End(range), None) => Ok(extent == Some(&range)),
            _ => Ok(false),
        }
    }
    pub(super) fn observe_proof_end(
        &mut self,
        extent: Option<&Range<usize>>,
        goals: &[tactics::ProofGoal],
    ) -> Result<(), NatDefinitionElabError> {
        if self.observes_goal(None, extent)? {
            self.observe_goals(goals)?;
        }
        Ok(())
    }
    pub(super) fn observe_goals(
        &mut self,
        goals: &[tactics::ProofGoal],
    ) -> Result<(), NatDefinitionElabError> {
        self.flush(true)?;
        let mut observed = Vec::new();
        for goal in goals {
            let target = self.instantiate(&goal.target)?;
            let locals = self.observation_locals(&goal.lctx, &[&target])?;
            observed.push(ObservedGoal {
                id: Some(goal.id.clone()),
                user_name: self
                    .goal_tags
                    .get(&goal.id)
                    .filter(|name| !name.is_anonymous())
                    .cloned(),
                target,
                locals,
                environment: self.txn.env.clone(),
            });
        }
        let probe = self.inspection.as_mut().expect("selected probe");
        probe.result = Some(SourceObservation::Goals {
            range: probe.site.range().clone(),
            goals: observed,
        });
        Err(failure(SourceInferenceError::ObservationComplete))
    }
}

#[cfg(test)]
mod expression_tests {
    use super::*;

    #[test]
    fn a_native_goal_retains_the_environment_used_for_its_observation() {
        let kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
        let source = "def pending (f : Nat → Nat) : Nat := f _";
        let goal = {
            let environment = crate::seed::bootstrap_nat_environment(kernel).unwrap();
            let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
            let Some(SourceObservation::Goals { mut goals, .. }) = declaration(
                parsed.syntax(),
                &environment,
                kernel,
                &SourceScope::default(),
                source.rfind('_').unwrap(),
                ObservationKind::TermGoal,
            )
            .unwrap() else {
                panic!("native term goal was not observed");
            };
            goals.pop().unwrap()
        };
        let mut inspector = goal.expression_inspector(kernel, 10_000).unwrap();
        assert_eq!(
            inspector.type_of(&goal.target).unwrap(),
            Some(Expr::sort(Level::one()))
        );
        let f = goal
            .locals
            .find_by_user_name(&Name::from_components(["f"]))
            .unwrap();
        let application = Expr::app(
            Expr::fvar(f.id.clone()),
            Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(7))),
        );
        assert_eq!(inspector.type_of(&application).unwrap(), Some(goal.target));
    }

    #[test]
    fn expression_types_preserve_dependent_locals_and_fresh_binder_identity() {
        let environment = Environment::new();
        let parameter = FVarId(Name::num(Name::from_components(["_fln_source"]), 0));
        let p = Expr::fvar(parameter.clone());
        let mut locals = LocalContext::new();
        locals.add_param(
            parameter,
            Name::from_components(["P"]),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        );
        let before = locals.clone();
        let mut inspector = ExpressionInspector::new(
            &environment,
            &locals,
            Budget::for_stack_bytes(2 * 1024 * 1024),
            10_000,
        )
        .unwrap();
        let binder = Name::from_components(["h"]);
        let identity = Expr::lam(
            binder.clone(),
            p.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        let expected = Expr::forall_e(binder, p.clone(), p.clone(), BinderInfo::Default);
        assert_eq!(
            inspector.type_of(&identity).unwrap(),
            Some(expected.clone())
        );
        assert_eq!(inspector.type_of(&identity).unwrap(), Some(expected));
        assert_eq!(
            inspector.type_of(&p).unwrap(),
            Some(Expr::sort(Level::zero()))
        );
        assert_eq!(locals, before);
        // Opening h at _fln_source.0 would alias P and infer Prop as h's type.
        assert_eq!(inspector.context.txn.lctx, before);
    }

    #[test]
    fn expression_inspection_is_bounded_and_does_not_guess_missing_context() {
        let environment = Environment::new();
        let locals = LocalContext::new();
        let kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
        assert!(ExpressionInspector::new(&environment, &locals, kernel, 0).is_err());
        let mut short = ExpressionInspector::new(&environment, &locals, kernel, 1).unwrap();
        assert!(matches!(
            short.type_of(&Expr::sort(Level::zero())),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(short.type_of(&Expr::sort(Level::zero())).is_err());
        let mut inspector =
            ExpressionInspector::new(&environment, &locals, kernel, 10_000).unwrap();
        assert_eq!(inspector.type_of(&Expr::bvar(0).unwrap()).unwrap(), None);
        assert_eq!(
            inspector
                .type_of(&Expr::const_(Name::from_components(["Missing"]), vec![]))
                .unwrap(),
            None
        );
        let u = Level::param(Name::from_components(["u"]));
        assert_eq!(
            inspector.type_of(&Expr::sort(u.clone())).unwrap(),
            Some(Expr::sort(u.succ().unwrap()))
        );
    }
}
