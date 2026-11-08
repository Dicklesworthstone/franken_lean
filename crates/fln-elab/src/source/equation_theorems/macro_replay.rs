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

    fn syntax(&mut self, syntax: &Syntax, work: &Work) -> Option<Arc<Syntax>> {
        let mut pending = vec![syntax];
        while let Some(node) = pending.pop() {
            self.charge(work)?;
            match node {
                Syntax::Node { kind, args, .. } => {
                    self.name(kind, work)?;
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
}

impl Recorder {
    fn record(&self, make: impl FnOnce(&mut Recording, &Work) -> Option<Event>) {
        let Ok(mut recording) = self.recording.lock() else {
            self.work.exhausted.store(true, Ordering::Relaxed);
            return;
        };
        let before = recording.remaining;
        let event = recording
            .charge(&self.work)
            .and_then(|()| make(&mut recording, &self.work));
        if let Some(event) = event {
            let work = before - recording.remaining;
            recording.entries.push(Arc::new(Entry { event, work }));
        }
    }

    fn source_scope(&self, scope: &SourceScope) -> SourceScope {
        let mut source = scope.clone();
        source.tactic_macros = Some(self.provider.clone());
        source
    }
}

impl TacticMacroExpander for Recorder {
    fn contains(&self, kind: &Name) -> bool {
        let result = self.provider.0.contains(kind);
        self.record(|recording, work| {
            recording.name(kind, work)?;
            Some(Event::Contains(kind.clone(), result))
        });
        result
    }

    fn enter_tactic(&self, depth: usize) -> Result<u64, TacticMacroError> {
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
                result.map(|expansion| match expansion {
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
                })
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
        let remaining = if self.txn.budget.max_heartbeats == 0 {
            MAX_TRACE_WORK
        } else {
            self.txn
                .budget
                .max_heartbeats
                .saturating_sub(self.txn.budget.heartbeats_consumed)
                .min(MAX_TRACE_WORK)
        };
        let mut recording = Recording {
            remaining,
            entries: Vec::new(),
        };
        let syntax = recording.syntax(syntax, &work);
        self.charge_equation_macro_work()?;
        let syntax = syntax.ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        let recorder = Arc::new(Recorder {
            provider,
            work,
            recording: Mutex::new(recording),
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
                if previous.as_ref() != row.as_ref() {
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
        self.charge_equation_macro_work()?;
        Ok(match term {
            Ok(term) if replay.complete() => Some(term),
            _ => None,
        })
    }
}
