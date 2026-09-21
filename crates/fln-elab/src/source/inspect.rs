//! Read-only observations from the real native term and tactic drivers.
//!
//! Inspection stops before the selected tactic, or after the selected term.
//! An unfinished proof is never manufactured into a declaration. The private
//! stop is non-recoverable by `try`/`first`, and ordinary admission has no probe.
use super::*;
use std::ops::Range;

/// Which elaboration boundary the caller wants to observe.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObservationKind {
    Goals,
    Term,
}

/// A live obligation, not an accepted proof. Types and locals are instantiated
/// through the same metavariable store used by the native tactic driver.
#[derive(Debug, Clone)]
pub struct ObservedGoal {
    pub target: Expr,
    pub locals: LocalContext,
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
}
impl SourceObservation {
    pub fn range(&self) -> Range<usize> {
        match self {
            Self::Goals { range, .. } | Self::Term { range, .. } => range.clone(),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
enum Site {
    Tactic(Range<usize>),
    By(Range<usize>),
    End(Range<usize>),
    Term(Range<usize>),
}
impl Site {
    fn range(&self) -> &Range<usize> {
        match self {
            Self::Tactic(r) | Self::By(r) | Self::End(r) | Self::Term(r) => r,
        }
    }
}
#[derive(Clone)]
pub(super) struct Probe {
    site: Site,
    result: Option<SourceObservation>,
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
    let mut context = Context::scoped(environment, kernel, scope);
    // There will be no final declaration admission to discharge earlier rigid
    // equations. Check them when generated instead of deferring to that door.
    context.attempt_depth = 1;
    let Some(site) = select(&mut context, syntax, offset, kind)? else {
        return Ok(None);
    };
    context.inspection = Some(Probe { site, result: None });
    match definition_in_context(syntax, &mut context) {
        Err(NatDefinitionElabError::Inference(SourceInferenceError::ObservationComplete)) => {
            Ok(context.inspection.and_then(|probe| probe.result))
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
        if wanted == ObservationKind::Term && matches!(node, Syntax::Ident { .. }) {
            sites.push(Site::Term(r));
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
            } else if kind.parent() == parser_kind(&["Tactic"])
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
    ) -> Result<LocalContext, NatDefinitionElabError> {
        let mut result = LocalContext::new();
        for local in source.decls() {
            self.tick()?;
            let mut local = local.clone();
            local.type_ = self.instantiate(&local.type_)?;
            local.value = local
                .value
                .as_ref()
                .map(|value| self.instantiate(value))
                .transpose()?;
            if let Some(value) = local.value {
                result.add_let(local.id, local.user_name, local.type_, value);
            } else {
                result.add_param(local.id, local.user_name, local.type_, local.binder_info);
            }
        }
        Ok(result)
    }
    pub(super) fn observes_term(&self, syntax: &Syntax) -> bool {
        let Some(Probe {
            site: Site::Term(range),
            ..
        }) = &self.inspection
        else {
            return false;
        };
        matches!(syntax, Syntax::Ident { .. })
            && syntax.info().pos(true).is_some_and(|p| p.0 == range.start)
            && syntax
                .info()
                .end_pos(true)
                .is_some_and(|p| p.0 == range.end)
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
        self.flush(true)?;
        let expression = self.instantiate(&term.value)?;
        let type_ = self.instantiate(&term.type_)?;
        let locals = self.observation_locals(&locals)?;
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
        if let Some(Probe {
            site: Site::By(range),
            ..
        }) = &self.inspection
            && keyword.info().pos(true).is_some_and(|p| p.0 == range.start)
        {
            return self.observe_goals(&[(goal.target.clone(), goal.lctx.clone())]);
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
        goals: &[(Expr, LocalContext)],
    ) -> Result<(), NatDefinitionElabError> {
        if self.observes_goal(None, extent)? {
            self.observe_goals(goals)?;
        }
        Ok(())
    }
    pub(super) fn observe_goals(
        &mut self,
        goals: &[(Expr, LocalContext)],
    ) -> Result<(), NatDefinitionElabError> {
        self.flush(true)?;
        let mut observed = Vec::new();
        for (target, locals) in goals {
            let target = self.instantiate(target)?;
            let locals = self.observation_locals(locals)?;
            observed.push(ObservedGoal { target, locals });
        }
        let probe = self.inspection.as_mut().expect("selected probe");
        probe.result = Some(SourceObservation::Goals {
            range: probe.site.range().clone(),
            goals: observed,
        });
        Err(failure(SourceInferenceError::ObservationComplete))
    }
}
