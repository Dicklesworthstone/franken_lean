//! Equation capture reuses the provider decisions made while checking each RHS.
//!
//! A macro provider is effectful: even a failed candidate, a miss, or allocation
//! of a tactic scope can affect its next answer. Recording belongs to an actual
//! row visit, not to a syntax kind or a global expansion cache. Checkpoints share
//! the active recorder (as they share the live provider), but completed rows are
//! ordinary transactional Context state. Capture has only a replay provider and
//! declines metadata if its requests do not consume the exact recorded trace.
use super::super::*;
use crate::tactic_macros::{
    TacticMacroError, TacticMacroExpander, TacticMacroExpansion, TacticMacroProvider,
};
use fln_syntax::source::SourceInfo;
use std::collections::HashMap;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, AtomicU64, Ordering},
};

// An unlimited elaboration budget still does not authorize an unbounded journal
// of provider responses. Ordinary finite budgets impose their remaining limit.
const MAX_TRACE_WORK: u64 = 1_000_000;

#[derive(Default)]
pub(in crate::source) struct Work {
    pending: AtomicU64,
    exhausted: AtomicBool,
    mismatched: AtomicBool,
}

impl Work {
    fn add(&self, amount: u64) {
        if self
            .pending
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |previous| {
                previous.checked_add(amount)
            })
            .is_err()
        {
            self.exhausted.store(true, Ordering::Relaxed);
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
enum Expansion {
    Expanded {
        syntax: Arc<Syntax>,
        no_fallback: bool,
    },
    Unsupported,
    Diagnostic {
        error: TacticMacroError,
        no_fallback: bool,
    },
    Exhausted,
}

#[derive(Clone, PartialEq, Eq)]
enum Event {
    Contains(Name, bool),
    Enter(usize, Result<u64, TacticMacroError>),
    Term {
        syntax: Arc<Syntax>,
        depth: usize,
        result: Result<Option<Arc<Syntax>>, TacticMacroError>,
    },
    Tactic {
        syntax: Arc<Syntax>,
        candidate: usize,
        scope: u64,
        depth: usize,
        result: Result<Expansion, TacticMacroError>,
    },
}

#[derive(Clone, PartialEq, Eq)]
struct Entry {
    event: Event,
    work: u64,
}

#[derive(Clone, PartialEq, Eq)]
pub(in crate::source) struct Row {
    syntax: Arc<Syntax>,
    depth: usize,
    terms: usize,
    finish: bool,
    work: u64,
    entries: Vec<Arc<Entry>>,
}

#[derive(Clone)]
enum Observed {
    Missing,
    Recorded(Arc<Row>),
    Ambiguous,
}

#[derive(Clone)]
struct Active {
    index: usize,
    syntax: Arc<Syntax>,
    depth: usize,
    terms: usize,
    finish: bool,
    limit: u64,
    recorder: Arc<Recorder>,
}

#[derive(Clone)]
pub(in crate::source) struct Rows {
    sources: HashMap<usize, usize>,
    rows: Vec<Observed>,
    active: Option<Active>,
    occurrences: Vec<usize>,
    prefixes: Arc<Mutex<Vec<Vec<Segment>>>>,
}

type Segment = Arc<Mutex<Vec<Arc<Entry>>>>;

impl Row {
    /// Fresh tactic scopes are allocation identities, not source-row identities.
    /// A bijection may rename those return values and their request uses only:
    /// every syntax, expansion result, diagnostic, and other input stays exact.
    fn same_expansions(&self, other: &Self) -> bool {
        if self.syntax != other.syntax
            || self.depth != other.depth
            || self.terms != other.terms
            || self.finish != other.finish
            || self.entries.len() != other.entries.len()
        {
            return false;
        }
        let mut forward = HashMap::new();
        let mut backward = HashMap::new();
        for (left, right) in self.entries.iter().zip(&other.entries) {
            match (&left.event, &right.event) {
                (Event::Enter(left_depth, Ok(left)), Event::Enter(right_depth, Ok(right))) => {
                    if left_depth != right_depth {
                        return false;
                    }
                    if let Some(mapped) = forward.get(left) {
                        if mapped != right {
                            return false;
                        }
                    } else {
                        if backward.contains_key(right) {
                            return false;
                        }
                        forward.insert(*left, *right);
                        backward.insert(*right, *left);
                    }
                }
                (
                    Event::Tactic {
                        syntax: left_syntax,
                        candidate: left_candidate,
                        scope: left_scope,
                        depth: left_depth,
                        result: left_result,
                    },
                    Event::Tactic {
                        syntax: right_syntax,
                        candidate: right_candidate,
                        scope: right_scope,
                        depth: right_depth,
                        result: right_result,
                    },
                ) => {
                    if left_syntax != right_syntax
                        || left_candidate != right_candidate
                        || left_depth != right_depth
                        || left_result != right_result
                        || forward.get(left_scope).unwrap_or(left_scope) != right_scope
                    {
                        return false;
                    }
                }
                (left, right) if left == right => {}
                _ => return false,
            }
        }
        true
    }
}

impl Rows {
    pub(super) fn new(alternatives: &[(Vec<&Syntax>, &Syntax)]) -> Self {
        Self {
            sources: alternatives
                .iter()
                .enumerate()
                .map(|(index, (_, rhs))| (std::ptr::from_ref(*rhs).addr(), index))
                .collect(),
            rows: vec![Observed::Missing; alternatives.len()],
            active: None,
            occurrences: vec![0; alternatives.len()],
            prefixes: Arc::new(Mutex::new(vec![Vec::new(); alternatives.len()])),
        }
    }

    pub(super) fn get(&self, index: usize) -> Option<Arc<Row>> {
        match self.rows.get(index)? {
            Observed::Recorded(row) => Some(row.clone()),
            Observed::Missing | Observed::Ambiguous => None,
        }
    }
}

struct Recording {
    remaining: u64,
    entries: Vec<Arc<Entry>>,
}

impl Recording {
    fn charge(&mut self, work: &Work) -> Option<()> {
        self.units(1, work)
    }

    fn units(&mut self, amount: u64, work: &Work) -> Option<()> {
        if amount > self.remaining {
            work.add(self.remaining);
            self.remaining = 0;
            work.exhausted.store(true, Ordering::Relaxed);
            return None;
        }
        self.remaining -= amount;
        work.add(amount);
        Some(())
    }

    fn bytes(&mut self, bytes: usize, work: &Work) -> Option<()> {
        self.units(u64::try_from(bytes).unwrap_or(u64::MAX), work)
    }

    fn name(&mut self, name: &Name, work: &Work) -> Option<()> {
        let mut name = name.clone();
        while !name.is_anonymous() {
            self.charge(work)?;
            if let LeafView::Str(component) = name.leaf_view() {
                self.bytes(component.len(), work)?;
            }
            name = name.parent();
        }
        Some(())
    }

    fn error(&mut self, error: &TacticMacroError, work: &Work) -> Option<TacticMacroError> {
        // Count through a bounded writer before cloning. This covers diagnostic
        // strings nested inside an Inconclusive as well as ordinary messages,
        // without allocating a formatted copy of an oversized error.
        struct Counter<'a> {
            recording: &'a mut Recording,
            work: &'a Work,
        }
        impl std::fmt::Write for Counter<'_> {
            fn write_str(&mut self, text: &str) -> std::fmt::Result {
                self.recording
                    .bytes(text.len(), self.work)
                    .ok_or(std::fmt::Error)
            }
        }
        std::fmt::write(
            &mut Counter {
                recording: self,
                work,
            },
            format_args!("{error:?}"),
        )
        .ok()?;
        Some(error.clone())
    }

    fn measure_syntax(&mut self, syntax: &Syntax, work: &Work) -> Option<()> {
        let mut pending = vec![syntax];
        while let Some(node) = pending.pop() {
            self.charge(work)?;
            match node {
                Syntax::Node { kind, args, .. } => {
                    self.name(kind, work)?;
                    // Bound the traversal frontier before retaining its edges.
                    self.units(args.len() as u64, work)?;
                    pending.extend(args);
                }
                Syntax::Atom { val, .. } => self.bytes(val.len(), work)?,
                Syntax::Ident {
                    raw_val,
                    val,
                    preresolved,
                    ..
                } => {
                    self.name(val, work)?;
                    if let Some(backing) = raw_val.owned_backing() {
                        // Keeping an Arc retains the whole quotation backing,
                        // even when its visible substring is only one byte.
                        self.bytes(backing.len(), work)?;
                    }
                    for resolution in preresolved {
                        use fln_syntax::tree::Preresolved;
                        self.charge(work)?;
                        match resolution {
                            Preresolved::Namespace { ns } => self.name(ns, work)?,
                            Preresolved::Decl { name, fields } => {
                                self.name(name, work)?;
                                self.units(fields.len() as u64, work)?;
                                for field in fields {
                                    self.bytes(field.len(), work)?;
                                }
                            }
                        }
                    }
                }
                Syntax::Missing => {}
            }
        }
        Some(())
    }

    fn syntax(&mut self, syntax: &Syntax, work: &Work) -> Option<Arc<Syntax>> {
        self.measure_syntax(syntax, work)?;
        // Syntax's Clone and equality both use heap worklists.
        Some(Arc::new(syntax.clone()))
    }

    fn expansion(&mut self, result: &TacticMacroExpansion, work: &Work) -> Option<Expansion> {
        Some(match result {
            TacticMacroExpansion::Expanded {
                syntax,
                no_fallback,
            } => Expansion::Expanded {
                syntax: self.syntax(syntax, work)?,
                no_fallback: *no_fallback,
            },
            TacticMacroExpansion::Unsupported => Expansion::Unsupported,
            TacticMacroExpansion::Diagnostic { error, no_fallback } => Expansion::Diagnostic {
                error: self.error(error, work)?,
                no_fallback: *no_fallback,
            },
            TacticMacroExpansion::Exhausted => Expansion::Exhausted,
        })
    }
}

struct Recorder {
    provider: TacticMacroProvider,
    work: Arc<Work>,
    recording: Mutex<Recording>,
    prefix: Segment,
    cursor: Mutex<Cursor>,
}

impl Recorder {
    fn record(&self, make: impl FnOnce(&mut Recording, &Work) -> Option<Event>) {
        let Ok(mut recording) = self.recording.lock() else {
            self.work.exhausted.store(true, Ordering::Relaxed);
            return;
        };
        let Ok(mut cursor) = self.cursor.lock() else {
            self.work.exhausted.store(true, Ordering::Relaxed);
            return;
        };
        let Ok(mut prefix) = self.prefix.lock() else {
            self.work.exhausted.store(true, Ordering::Relaxed);
            return;
        };
        if cursor.failed || cursor.next != prefix.len() {
            cursor.failed = true;
            self.work.mismatched.store(true, Ordering::Relaxed);
            return;
        }
        let before = recording.remaining;
        let event = recording
            .charge(&self.work)
            .and_then(|()| make(&mut recording, &self.work));
        if let Some(event) = event {
            let work = before - recording.remaining;
            let entry = Arc::new(Entry { event, work });
            prefix.push(entry.clone());
            cursor.next += 1;
            recording.entries.push(entry);
        }
    }

    fn ready(&self) -> Result<(), TacticMacroError> {
        if self.work.mismatched.load(Ordering::Relaxed) {
            return Err(mismatch());
        }
        let remaining = self.recording.lock().map_err(|_| mismatch())?.remaining;
        if remaining == 0 || self.work.exhausted.load(Ordering::Relaxed) {
            self.work.exhausted.store(true, Ordering::Relaxed);
            return Err(trace_limit(0, 1));
        }
        Ok(())
    }

    /// A semantic body retry consumes exactly the calls already executed for
    /// this physical row occurrence. A failed elaboration leaves its prefix in
    /// shared state; only its previously unseen suffix reaches the live provider.
    fn cached<T>(
        &self,
        read: impl FnOnce(Event) -> Option<T>,
    ) -> Result<Option<T>, TacticMacroError> {
        self.ready()?;
        let mut recording = self.recording.lock().map_err(|_| mismatch())?;
        let mut cursor = self.cursor.lock().map_err(|_| mismatch())?;
        if cursor.failed {
            return Err(mismatch());
        }
        let entry = self
            .prefix
            .lock()
            .map_err(|_| mismatch())?
            .get(cursor.next)
            .cloned();
        let Some(entry) = entry else {
            return Ok(None);
        };
        let remaining = recording.remaining;
        if recording.units(entry.work, &self.work).is_none() {
            return Err(trace_limit(remaining, entry.work));
        }
        let Some(answer) = read(entry.event.clone()) else {
            cursor.failed = true;
            self.work.mismatched.store(true, Ordering::Relaxed);
            return Err(mismatch());
        };
        cursor.next += 1;
        recording.entries.push(entry);
        Ok(Some(answer))
    }

    fn source_scope(&self, scope: &SourceScope) -> SourceScope {
        let mut source = scope.clone();
        source.tactic_macros = Some(self.provider.clone());
        source
    }
}

impl TacticMacroExpander for Recorder {
    fn contains(&self, kind: &Name) -> bool {
        match self.cached(|event| match event {
            Event::Contains(recorded, result) if &recorded == kind => Some(result),
            _ => None,
        }) {
            Ok(Some(result)) => return result,
            Ok(None) => {}
            Err(_) => return false,
        }
        let result = self.provider.0.contains(kind);
        self.record(|recording, work| {
            recording.name(kind, work)?;
            Some(Event::Contains(kind.clone(), result))
        });
        result
    }

    fn enter_tactic(&self, depth: usize) -> Result<u64, TacticMacroError> {
        if let Some(result) = self.cached(|event| match event {
            Event::Enter(recorded, result) if recorded == depth => Some(result),
            _ => None,
        })? {
            return result;
        }
        let result = self.provider.0.enter_tactic(depth);
        self.record(|recording, work| {
            Some(Event::Enter(
                depth,
                match &result {
                    Ok(scope) => Ok(*scope),
                    Err(error) => Err(recording.error(error, work)?),
                },
            ))
        });
        result
    }

    fn expand_tactic(
        &self,
        syntax: &Syntax,
        candidate: usize,
        macro_scope: u64,
        depth: usize,
        environment: &Environment,
        scope: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        if let Some(result) = self.cached(|event| match event {
            Event::Tactic {
                syntax: recorded,
                candidate: index,
                scope: entered,
                depth: at,
                result,
            } if recorded.as_ref() == syntax
                && index == candidate
                && entered == macro_scope
                && at == depth =>
            {
                Some(result)
            }
            _ => None,
        })? {
            return result.map(expansion_result);
        }
        let result = self.provider.0.expand_tactic(
            syntax,
            candidate,
            macro_scope,
            depth,
            environment,
            &self.source_scope(scope),
        );
        self.record(|recording, work| {
            Some(Event::Tactic {
                syntax: recording.syntax(syntax, work)?,
                candidate,
                scope: macro_scope,
                depth,
                result: match &result {
                    Ok(expansion) => Ok(recording.expansion(expansion, work)?),
                    Err(error) => Err(recording.error(error, work)?),
                },
            })
        });
        result
    }

    fn expand_term(
        &self,
        syntax: &Syntax,
        depth: usize,
        environment: &Environment,
        scope: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        if let Some(result) = self.cached(|event| match event {
            Event::Term {
                syntax: recorded,
                depth: at,
                result,
            } if recorded.as_ref() == syntax && at == depth => Some(result),
            _ => None,
        })? {
            return result.map(|syntax| syntax.map(|syntax| syntax.as_ref().clone()));
        }
        let result =
            self.provider
                .0
                .expand_term(syntax, depth, environment, &self.source_scope(scope));
        self.record(|recording, work| {
            Some(Event::Term {
                syntax: recording.syntax(syntax, work)?,
                depth,
                result: match &result {
                    Ok(Some(syntax)) => Ok(Some(recording.syntax(syntax, work)?)),
                    Ok(None) => Ok(None),
                    Err(error) => Err(recording.error(error, work)?),
                },
            })
        });
        result
    }
}

#[derive(Default)]
struct Cursor {
    next: usize,
    failed: bool,
}

struct Replay {
    row: Arc<Row>,
    work: Arc<Work>,
    cursor: Mutex<Cursor>,
}

fn mismatch() -> TacticMacroError {
    TacticMacroError::Unsupported("equation capture differs from the checked macro trace".into())
}

fn trace_limit(allowed: u64, observed: u64) -> TacticMacroError {
    TacticMacroError::Inconclusive(Box::new(
        fln_core::outcome::Inconclusive::resource(fln_core::outcome::ResourceUsage {
            reason: fln_core::diag::ResourceReason::StructuralBudget {
                unit: fln_core::diag::StructuralUnit::ExpandedWeight,
            },
            allowed,
            observed,
        })
        .with_progress("reusing equation RHS macro answers"),
    ))
}

fn expansion_result(expansion: Expansion) -> TacticMacroExpansion {
    match expansion {
        Expansion::Expanded {
            syntax,
            no_fallback,
        } => TacticMacroExpansion::Expanded {
            syntax: syntax.as_ref().clone(),
            no_fallback,
        },
        Expansion::Unsupported => TacticMacroExpansion::Unsupported,
        Expansion::Diagnostic { error, no_fallback } => {
            TacticMacroExpansion::Diagnostic { error, no_fallback }
        }
        Expansion::Exhausted => TacticMacroExpansion::Exhausted,
    }
}

impl Replay {
    fn next(&self) -> Result<Event, TacticMacroError> {
        let mut cursor = self.cursor.lock().map_err(|_| mismatch())?;
        if cursor.failed {
            return Err(mismatch());
        }
        let Some(entry) = self.row.entries.get(cursor.next) else {
            cursor.failed = true;
            return Err(mismatch());
        };
        cursor.next += 1;
        // This covers the exact structural comparison and the returned syntax
        // copy, as well as the provider call itself. No live implementation is
        // retained by a replay provider.
        self.work.add(entry.work);
        Ok(entry.event.clone())
    }

    fn fail<T>(&self) -> Result<T, TacticMacroError> {
        if let Ok(mut cursor) = self.cursor.lock() {
            cursor.failed = true;
        }
        Err(mismatch())
    }

    fn complete(&self) -> bool {
        self.cursor
            .lock()
            .is_ok_and(|cursor| !cursor.failed && cursor.next == self.row.entries.len())
    }
}

impl TacticMacroExpander for Replay {
    fn contains(&self, kind: &Name) -> bool {
        match self.next() {
            Ok(Event::Contains(recorded, result)) if &recorded == kind => result,
            _ => self.fail::<bool>().unwrap_or(false),
        }
    }

    fn enter_tactic(&self, depth: usize) -> Result<u64, TacticMacroError> {
        match self.next()? {
            Event::Enter(recorded, result) if recorded == depth => result,
            _ => self.fail(),
        }
    }

    fn expand_tactic(
        &self,
        syntax: &Syntax,
        candidate: usize,
        macro_scope: u64,
        depth: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<TacticMacroExpansion, TacticMacroError> {
        match self.next()? {
            Event::Tactic {
                syntax: recorded,
                candidate: recorded_candidate,
                scope,
                depth: recorded_depth,
                result,
            } if recorded.as_ref() == syntax
                && recorded_candidate == candidate
                && scope == macro_scope
                && recorded_depth == depth =>
            {
                result.map(expansion_result)
            }
            _ => self.fail(),
        }
    }

    fn expand_term(
        &self,
        syntax: &Syntax,
        depth: usize,
        _: &Environment,
        _: &SourceScope,
    ) -> Result<Option<Syntax>, TacticMacroError> {
        match self.next()? {
            Event::Term {
                syntax: recorded,
                depth: recorded_depth,
                result,
            } if recorded.as_ref() == syntax && recorded_depth == depth => {
                result.map(|syntax| syntax.map(|syntax| syntax.as_ref().clone()))
            }
            _ => self.fail(),
        }
    }
}

/// Unsupported reconstruction can decline optional metadata. A resource stop,
/// cancellation, or internal fault still prevents a completed answer.
pub(super) fn capture_result<T>(
    result: Result<T, NatDefinitionElabError>,
) -> Result<Option<T>, NatDefinitionElabError> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(problem) if capture_stopped(&problem) => Err(problem),
        Err(_) => Ok(None),
    }
}

/// Preserve an already observed terminal cause when accounting discovers a
/// second stop. In particular, an oversized cancellation diagnostic must not
/// be replaced by the resource limit encountered while recording that error.
pub(in crate::source) fn capture_stopped(problem: &NatDefinitionElabError) -> bool {
    let nonanswer = |outcome: &Outcome<Verdict>| {
        matches!(
            outcome,
            Outcome::Inconclusive(_) | Outcome::InternalFault(_)
        )
    };
    match problem {
        NatDefinitionElabError::Inference(
            SourceInferenceError::ResourceLimit
            | SourceInferenceError::ArithmeticInconclusive(_)
            | SourceInferenceError::NativeEvaluationInconclusive(_)
            | SourceInferenceError::NativeEvaluation(crate::native::NativeEvaluationError::Fault(_))
            | SourceInferenceError::TacticMacro(
                TacticMacroError::Inconclusive(_) | TacticMacroError::InternalFault(_),
            )
            | SourceInferenceError::Universe(
                crate::universe::UniverseInstantiationError::VisitLimit { .. }
                | crate::universe::UniverseInstantiationError::LevelTooDeep(_),
            ),
        ) => true,
        NatDefinitionElabError::Inference(SourceInferenceError::TypeObligation(outcome)) => {
            nonanswer(outcome)
        }
        NatDefinitionElabError::Inference(SourceInferenceError::Unification(error)) => {
            match error.as_ref() {
                UnificationError::Cancelled
                | UnificationError::StepLimit { .. }
                | UnificationError::NodeLimit { .. }
                | UnificationError::AssignmentLimit { .. }
                | UnificationError::HeartbeatLimit
                | UnificationError::Universe(
                    crate::universe::UniverseInstantiationError::VisitLimit { .. }
                    | crate::universe::UniverseInstantiationError::LevelTooDeep(_),
                ) => true,
                UnificationError::ConversionCheck { outcome }
                | UnificationError::AssignmentCheck { outcome, .. }
                | UnificationError::ConstraintCheck { outcome, .. } => nonanswer(outcome),
                _ => false,
            }
        }
        _ => false,
    }
}

pub(in crate::source) fn parts(syntax: &Syntax) -> Option<(usize, &Syntax)> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    if kind != &parser_kind(&["Term", "equationRhs"]) {
        return None;
    }
    let [Syntax::Atom { val, .. }, body] = args.as_slice() else {
        return None;
    };
    Some((val.parse().ok()?, body))
}

impl Context {
    pub(in crate::source) fn begin_equation_macro_pass(&mut self, syntax: &Syntax) {
        if self.equation_pattern_source
            == Some(std::ptr::from_ref(super::capture::under_lambdas(syntax)).addr())
            && let Some(rows) = &mut self.equation_macros
            && rows.active.is_none()
        {
            // A new semantic trial begins at the first physical occurrence of
            // each row. Copies within this trial still have distinct segments.
            rows.occurrences.fill(0);
        }
    }

    /// Mark borrowed source rows before any native preparation can replace the
    /// containing tree. The markers then travel with the actual matrix copies.
    pub(in crate::source) fn mark_equation_source(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Syntax>, NatDefinitionElabError> {
        if self.equation_macros.is_none() {
            return Ok(None);
        }
        let mut scan = vec![syntax];
        let mut found = false;
        while let Some(node) = scan.pop() {
            self.tick()?;
            if self.watches_equation_rhs(node) {
                found = true;
                break;
            }
            if let Syntax::Node { args, .. } = node {
                scan.extend(args);
            }
        }
        if !found {
            return Ok(None);
        }
        let work = self
            .equation_macro_work
            .clone()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let mut measurement = Recording {
            remaining: self.equation_trace_limit(),
            entries: Vec::new(),
        };
        let measured = measurement.measure_syntax(syntax, &work);
        self.charge_equation_macro_work()?;
        measured.ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        enum Task<'a> {
            Visit(&'a Syntax),
            Build(&'a Syntax, usize),
        }
        let mut tasks = vec![Task::Visit(syntax)];
        let mut built = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(node @ Syntax::Node { args, .. }) => {
                    tasks.push(Task::Build(node, built.len()));
                    tasks.extend(args.iter().rev().map(Task::Visit));
                }
                Task::Visit(leaf) => built.push(self.mark_equation_rhs(leaf, leaf.clone())),
                Task::Build(source @ Syntax::Node { info, kind, .. }, start) => {
                    let node = Syntax::Node {
                        info: *info,
                        kind: kind.clone(),
                        args: built.split_off(start),
                    };
                    built.push(self.mark_equation_rhs(source, node));
                }
                Task::Build(..) => return Err(failure(SourceInferenceError::Scope)),
            }
        }
        Ok(built.pop())
    }

    /// The complete ordered marker family identifies the watched root after a
    /// preparation pass has replaced its allocation. A nested match does not
    /// have these markers on its alternatives' direct RHSs.
    pub(in crate::source) fn equation_root_rows(&self, alternatives: &[Syntax]) -> bool {
        let Some(rows) = &self.equation_macros else {
            return false;
        };
        alternatives.len() == rows.rows.len()
            && alternatives.iter().enumerate().all(|(index, alternative)| {
                let Syntax::Node { kind, args, .. } = alternative else {
                    return false;
                };
                kind == &parser_kind(&["Term", "matchAlt"])
                    && args.len() == 4
                    && parts(&args[3]).is_some_and(|(row, _)| row == index)
            })
    }

    fn equation_trace_limit(&self) -> u64 {
        if self.txn.budget.max_heartbeats == 0 {
            MAX_TRACE_WORK
        } else {
            self.txn
                .budget
                .max_heartbeats
                .saturating_sub(self.txn.budget.heartbeats_consumed)
                .min(MAX_TRACE_WORK)
        }
    }

    pub(in crate::source) fn watches_equation_rhs(&self, syntax: &Syntax) -> bool {
        self.equation_macros.as_ref().is_some_and(|rows| {
            rows.sources
                .contains_key(&std::ptr::from_ref(syntax).addr())
        })
    }

    pub(in crate::source) fn mark_equation_rhs(&self, source: &Syntax, syntax: Syntax) -> Syntax {
        let Some(index) = self
            .equation_macros
            .as_ref()
            .and_then(|rows| rows.sources.get(&std::ptr::from_ref(source).addr()))
        else {
            return syntax;
        };
        // This marker is copied with a matrix row's existing coverage witness.
        // Different specializations therefore retain the same original row.
        Syntax::node(
            parser_kind(&["Term", "equationRhs"]),
            vec![
                Syntax::Atom {
                    info: SourceInfo::None,
                    val: index.to_string(),
                },
                syntax,
            ],
        )
    }

    pub(in crate::source) fn begin_equation_rhs(
        &mut self,
        index: usize,
        syntax: &Syntax,
        finish: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(rows) = &self.equation_macros else {
            return Ok(false);
        };
        if rows.active.is_some() || index >= rows.rows.len() {
            return Ok(false);
        }
        let Some(provider) = self.source_scope.tactic_macros.clone() else {
            return Ok(false);
        };
        let Some(work) = self.equation_macro_work.clone() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let remaining = self.equation_trace_limit();
        let mut recording = Recording {
            remaining,
            entries: Vec::new(),
        };
        let syntax = recording.syntax(syntax, &work);
        self.charge_equation_macro_work()?;
        let syntax = syntax.ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        let rows = self.equation_macros.as_mut().expect("watched rows");
        let occurrence = rows.occurrences[index];
        rows.occurrences[index] = occurrence
            .checked_add(1)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        let prefix = {
            let mut prefixes = rows
                .prefixes
                .lock()
                .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
            let segments = &mut prefixes[index];
            if occurrence == segments.len() {
                recording
                    .charge(&work)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                segments.push(Arc::new(Mutex::new(Vec::new())));
            }
            segments
                .get(occurrence)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?
        };
        let recorder = Arc::new(Recorder {
            provider,
            work,
            recording: Mutex::new(recording),
            prefix,
            cursor: Mutex::default(),
        });
        let active = Active {
            index,
            syntax,
            depth: self.tactic_macro_depth,
            terms: self.tactic_macro_terms,
            finish,
            limit: remaining,
            recorder: recorder.clone(),
        };
        self.equation_macros.as_mut().expect("watched rows").active = Some(active);
        self.source_scope.tactic_macros = Some(TacticMacroProvider(recorder));
        Ok(true)
    }

    pub(in crate::source) fn finish_equation_rhs(&mut self) -> Result<(), NatDefinitionElabError> {
        self.charge_equation_macro_work()?;
        let active = self
            .equation_macros
            .as_mut()
            .and_then(|rows| rows.active.take())
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        self.source_scope.tactic_macros = Some(active.recorder.provider.clone());
        let recording = active
            .recorder
            .recording
            .lock()
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        let cursor = active
            .recorder
            .cursor
            .lock()
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        let prefix = active
            .recorder
            .prefix
            .lock()
            .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
        if cursor.failed || cursor.next != prefix.len() {
            active
                .recorder
                .work
                .mismatched
                .store(true, Ordering::Relaxed);
            return Err(failure(SourceInferenceError::TacticMacro(mismatch())));
        }
        let row = Arc::new(Row {
            syntax: active.syntax,
            depth: active.depth,
            terms: active.terms,
            finish: active.finish,
            work: active.limit - recording.remaining,
            entries: recording.entries.clone(),
        });
        active.recorder.work.add(row.entries.len() as u64);
        let observed = &mut self.equation_macros.as_mut().expect("watched rows").rows[active.index];
        match observed {
            Observed::Missing => *observed = Observed::Recorded(row),
            Observed::Recorded(previous) => {
                // The same source row can be visited under several refinements.
                // Never manufacture one equation from incompatible occurrences.
                active.recorder.work.add(row.work);
                if !previous.same_expansions(&row) {
                    *observed = Observed::Ambiguous;
                }
            }
            Observed::Ambiguous => {}
        }
        self.charge_equation_macro_work()
    }

    pub(in crate::source) fn clear_equation_macros(&mut self) {
        if let Some(active) = self
            .equation_macros
            .as_mut()
            .and_then(|rows| rows.active.take())
        {
            self.source_scope.tactic_macros = Some(active.recorder.provider.clone());
        }
        self.equation_macros = None;
    }

    pub(in crate::source) fn charge_equation_macro_work(
        &mut self,
    ) -> Result<(), NatDefinitionElabError> {
        let Some(work) = &self.equation_macro_work else {
            return Ok(());
        };
        let amount = work.pending.swap(0, Ordering::Relaxed);
        self.txn.budget.heartbeats_consumed = self
            .txn
            .budget
            .heartbeats_consumed
            .checked_add(amount)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        if work.exhausted.load(Ordering::Relaxed)
            || (self.txn.budget.max_heartbeats != 0
                && self.txn.budget.heartbeats_consumed > self.txn.budget.max_heartbeats)
        {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        if work.mismatched.load(Ordering::Relaxed) {
            return Err(failure(SourceInferenceError::TacticMacro(mismatch())));
        }
        Ok(())
    }

    pub(super) fn replay_equation_rhs(
        &mut self,
        row: Arc<Row>,
        expected: Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if !row.finish {
            return Ok(None);
        }
        let work = self
            .equation_macro_work
            .get_or_insert_with(|| Arc::new(Work::default()))
            .clone();
        let replay = Arc::new(Replay {
            row: row.clone(),
            work,
            cursor: Mutex::new(Cursor {
                next: 0,
                failed: false,
            }),
        });
        let previous = self
            .source_scope
            .tactic_macros
            .replace(TacticMacroProvider(replay.clone()));
        let depth = std::mem::replace(&mut self.tactic_macro_depth, row.depth);
        let terms = std::mem::replace(&mut self.tactic_macro_terms, row.terms);
        // The recorded tree already passed matrix/notation preparation. Enter
        // at the same native Visit as the actual branch, without a new root
        // application guard or speculative pattern-macro execution.
        let term = self
            .term_prepared(&row.syntax, Some(expected))
            .and_then(|term| self.finish(term));
        self.source_scope.tactic_macros = previous;
        self.tactic_macro_depth = depth;
        self.tactic_macro_terms = terms;
        let work = self.charge_equation_macro_work();
        let term = capture_result(term)?;
        work?;
        Ok(match term {
            Some(term) if replay.complete() => Some(term),
            _ => None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;

    #[derive(Default)]
    struct Probe(AtomicUsize);

    impl TacticMacroExpander for Probe {
        fn contains(&self, _: &Name) -> bool {
            self.0.fetch_add(1, Ordering::Relaxed);
            false
        }

        fn enter_tactic(&self, _: usize) -> Result<u64, TacticMacroError> {
            Ok(self.0.fetch_add(1, Ordering::Relaxed) as u64)
        }

        fn expand_term(
            &self,
            _: &Syntax,
            _: usize,
            _: &Environment,
            _: &SourceScope,
        ) -> Result<Option<Syntax>, TacticMacroError> {
            self.0.fetch_add(1, Ordering::Relaxed);
            Ok(None)
        }

        fn expand_tactic(
            &self,
            _: &Syntax,
            _: usize,
            _: u64,
            _: usize,
            _: &Environment,
            _: &SourceScope,
        ) -> Result<TacticMacroExpansion, TacticMacroError> {
            self.0.fetch_add(1, Ordering::Relaxed);
            Ok(TacticMacroExpansion::Unsupported)
        }
    }

    fn recorder(provider: &Arc<Probe>, prefix: Segment, limit: u64) -> Recorder {
        Recorder {
            provider: TacticMacroProvider(provider.clone()),
            work: Arc::default(),
            recording: Mutex::new(Recording {
                remaining: limit,
                entries: Vec::new(),
            }),
            prefix,
            cursor: Mutex::default(),
        }
    }

    fn context(provider: &Arc<Probe>, syntax: &Syntax) -> Context {
        let mut context = Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        );
        context.source_scope.tactic_macros = Some(TacticMacroProvider(provider.clone()));
        context.equation_macros = Some(Rows::new(&[(Vec::new(), syntax)]));
        context.equation_macro_work = Some(Arc::default());
        context.equation_pattern_source = Some(std::ptr::from_ref(syntax).addr());
        context
    }

    #[test]
    fn semantic_retry_reuses_partial_effects_and_only_executes_the_new_suffix() {
        let provider = Arc::new(Probe::default());
        let prefix = Arc::new(Mutex::default());
        let initial = recorder(&provider, prefix.clone(), 1024);
        let kind = Name::from_components(["unregistered"]);
        let environment = Environment::new();
        let scope = SourceScope::default();
        assert!(!initial.contains(&kind));
        assert_eq!(initial.enter_tactic(0).unwrap(), 1);
        // A failed body can leave its RHS frame unfinished. The retry must
        // retain the callbacks that already happened before that failure.
        drop(initial);
        let retry = recorder(&provider, prefix, 1024);
        assert!(!retry.contains(&kind));
        assert_eq!(retry.enter_tactic(0).unwrap(), 1);
        assert!(
            retry
                .expand_term(&Syntax::Missing, 0, &environment, &scope)
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            retry
                .expand_tactic(&Syntax::Missing, 0, 1, 0, &environment, &scope)
                .unwrap(),
            TacticMacroExpansion::Unsupported
        ));
        assert_eq!(provider.0.load(Ordering::Relaxed), 4);

        let recording = retry.recording.lock().unwrap();
        let replay = Replay {
            row: Arc::new(Row {
                syntax: Arc::new(Syntax::Missing),
                depth: 0,
                terms: 0,
                finish: true,
                work: 1024 - recording.remaining,
                entries: recording.entries.clone(),
            }),
            work: Arc::default(),
            cursor: Mutex::default(),
        };
        assert!(!replay.contains(&kind));
        assert_eq!(replay.enter_tactic(0).unwrap(), 1);
        assert!(
            replay
                .expand_term(&Syntax::Missing, 0, &environment, &scope)
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            replay
                .expand_tactic(&Syntax::Missing, 0, 1, 0, &environment, &scope)
                .unwrap(),
            TacticMacroExpansion::Unsupported
        ));
        assert!(replay.complete());
        assert_eq!(provider.0.load(Ordering::Relaxed), 4);
    }

    #[test]
    fn changed_retry_inputs_latch_without_invoking_the_live_provider() {
        for contains in [false, true] {
            let provider = Arc::new(Probe::default());
            let prefix = Arc::new(Mutex::default());
            let initial = recorder(&provider, prefix.clone(), 1024);
            let environment = Environment::new();
            let scope = SourceScope::default();
            if contains {
                assert!(!initial.contains(&Name::from_components(["original"])));
            } else {
                initial
                    .expand_term(&Syntax::Missing, 0, &environment, &scope)
                    .unwrap();
            }
            let retry = recorder(&provider, prefix, 1024);
            if contains {
                assert!(!retry.contains(&Name::from_components(["changed"])));
            } else {
                let changed = Syntax::atom(SourceInfo::None, "changed");
                assert!(matches!(
                    retry.expand_term(&changed, 0, &environment, &scope),
                    Err(TacticMacroError::Unsupported(_))
                ));
            }
            assert!(retry.work.mismatched.load(Ordering::Relaxed));
            assert!(matches!(
                retry.enter_tactic(0),
                Err(TacticMacroError::Unsupported(_))
            ));
            assert_eq!(provider.0.load(Ordering::Relaxed), 1);

            // `contains` has no Result channel. Context rollback must still
            // expose its exact mismatch before ordinary tactic recovery.
            let mut context = context(&provider, &Syntax::Missing);
            context.equation_macro_work = Some(retry.work.clone());
            let checkpoint = context.clone();
            for mut state in [context, checkpoint] {
                assert!(matches!(
                    state.charge_equation_macro_work(),
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::TacticMacro(TacticMacroError::Unsupported(_))
                    ))
                ));
            }
        }
    }

    #[test]
    fn a_shorter_successful_retry_cannot_certify_an_equation_row() {
        let provider = Arc::new(Probe::default());
        let syntax = Syntax::Missing;
        let mut context = context(&provider, &syntax);
        let checkpoint = context.clone();
        assert!(context.begin_equation_rhs(0, &syntax, true).unwrap());
        let initial = context.source_scope.tactic_macros.clone().unwrap();
        assert!(!initial.0.contains(&Name::anonymous()));
        assert_eq!(initial.0.enter_tactic(0).unwrap(), 1);
        // Semantic retry restores ordinary context state, while the shared
        // external-callback prefix survives the abandoned first visit.
        context = checkpoint;
        assert!(context.begin_equation_rhs(0, &syntax, true).unwrap());
        let retry = context.source_scope.tactic_macros.clone().unwrap();
        assert!(!retry.0.contains(&Name::anonymous()));
        assert!(matches!(
            context.finish_equation_rhs(),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::TacticMacro(TacticMacroError::Unsupported(_))
            ))
        ));
        assert!(context.equation_macros.as_ref().unwrap().get(0).is_none());
        assert_eq!(provider.0.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn semantic_retries_keep_physical_matrix_occurrences_distinct() {
        let provider = Arc::new(Probe::default());
        let syntax = Syntax::Missing;
        let mut context = context(&provider, &syntax);
        for _ in 0..2 {
            context.begin_equation_macro_pass(&syntax);
            for expected_scope in [1, 3] {
                assert!(context.begin_equation_rhs(0, &syntax, true).unwrap());
                // Nested entry during an active row is not a semantic retry.
                context.begin_equation_macro_pass(&syntax);
                let current = context.source_scope.tactic_macros.clone().unwrap();
                assert!(!current.0.contains(&Name::anonymous()));
                assert_eq!(current.0.enter_tactic(0).unwrap(), expected_scope);
                context.finish_equation_rhs().unwrap();
            }
            let rows = context.equation_macros.as_ref().unwrap();
            assert_eq!(rows.prefixes.lock().unwrap()[0].len(), 2);
            assert!(rows.get(0).is_some());
            assert_eq!(provider.0.load(Ordering::Relaxed), 4);
        }
    }

    #[test]
    fn exhausted_recording_and_cached_work_survive_context_rollback() {
        let provider = Arc::new(Probe::default());
        let recording = recorder(&provider, Arc::new(Mutex::default()), 0);
        assert!(!recording.contains(&Name::anonymous()));
        assert_eq!(provider.0.load(Ordering::Relaxed), 0);
        let mut context = context(&provider, &Syntax::Missing);
        context.equation_macro_work = Some(recording.work.clone());
        let checkpoint = context.clone();
        for mut state in [context, checkpoint] {
            assert!(matches!(
                state.charge_equation_macro_work(),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                ))
            ));
        }

        let prefix = Arc::new(Mutex::default());
        let initial = recorder(&provider, prefix.clone(), 1024);
        assert!(!initial.contains(&Name::from_components(["longer"])));
        let retry = recorder(&provider, prefix, 1);
        assert!(!retry.contains(&Name::from_components(["longer"])));
        assert!(retry.work.exhausted.load(Ordering::Relaxed));
        assert_eq!(retry.recording.lock().unwrap().remaining, 0);
        assert_eq!(provider.0.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn frozen_tactic_replay_checks_the_exact_candidate_and_scope() {
        for (candidate, scope) in [(1, 17), (0, 18)] {
            let replay = Replay {
                row: Arc::new(Row {
                    syntax: Arc::new(Syntax::Missing),
                    depth: 0,
                    terms: 0,
                    finish: true,
                    work: 1,
                    entries: vec![Arc::new(Entry {
                        event: Event::Tactic {
                            syntax: Arc::new(Syntax::Missing),
                            candidate: 0,
                            scope: 17,
                            depth: 0,
                            result: Ok(Expansion::Unsupported),
                        },
                        work: 1,
                    })],
                }),
                work: Arc::default(),
                cursor: Mutex::default(),
            };
            assert!(matches!(
                replay.expand_tactic(
                    &Syntax::Missing,
                    candidate,
                    scope,
                    0,
                    &Environment::new(),
                    &SourceScope::default()
                ),
                Err(TacticMacroError::Unsupported(_))
            ));
            assert!(!replay.complete());
        }
    }

    #[test]
    fn retained_syntax_and_traversal_frontiers_have_finite_bounds() {
        use fln_syntax::{
            source::{BytePos, ByteSpan},
            tree::{Preresolved, RawIdentifier},
        };
        let backing = Syntax::Ident {
            info: SourceInfo::None,
            raw_val: RawIdentifier::owned(
                Arc::from("x".repeat(1024)),
                ByteSpan::new(BytePos(0), BytePos(1)).unwrap(),
            )
            .unwrap(),
            val: Name::anonymous(),
            preresolved: Vec::new(),
        };
        let frontier = Syntax::node(Name::anonymous(), vec![Syntax::Missing; 1024]);
        let empty_fields = Syntax::Ident {
            info: SourceInfo::None,
            raw_val: RawIdentifier::default(),
            val: Name::anonymous(),
            preresolved: vec![Preresolved::Decl {
                name: Name::anonymous(),
                fields: vec![String::new(); 1024],
            }],
        };
        for syntax in [backing, frontier, empty_fields] {
            let mut recording = Recording {
                remaining: 8,
                entries: Vec::new(),
            };
            let work = Work::default();
            assert!(recording.syntax(&syntax, &work).is_none());
            assert!(work.exhausted.load(Ordering::Relaxed));
            assert_eq!(recording.remaining, 0);
            assert_eq!(work.pending.load(Ordering::Relaxed), 8);
        }
        let provider = Arc::new(Probe::default());
        let mut context = context(&provider, &Syntax::Missing);
        context.txn.budget.max_heartbeats = 0;
        assert_eq!(context.equation_trace_limit(), MAX_TRACE_WORK);
    }
}
