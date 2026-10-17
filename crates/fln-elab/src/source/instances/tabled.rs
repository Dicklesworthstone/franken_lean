//! Shared instance generators and transactional consumers.
//!
//! A completed-answer cache alone cannot implement the pin's search order.
//! All consumers waiting on a query see every new answer, and their resumption
//! stack runs before the next generator (Lean/Meta/SynthInstance.lean `consume`,
//! `addAnswer`, `resume`, `step`). This matters when a later prerequisite rules
//! out an answer that an earlier sibling has also consumed.
use super::*;
use std::collections::HashMap;
use std::rc::Rc;

const MAX_TABLE_EVENTS: usize = MAX_CANDIDATE_ATTEMPTS * 16;
const MAX_TABLE_KEY_UNITS: usize = 65_536;

struct Answer {
    value: Expr,
    type_: Expr,
    size: u64,
}

struct Consumer {
    query: usize,
    context: Context,
    value: Expr,
    subgoals: Vec<MVarId>,
    depth: usize,
    size: u64,
}

struct Waiter {
    consumer: Rc<Consumer>,
    goal: Rc<Frame>,
}

struct Query {
    frame: Rc<Frame>,
    answers: Vec<Rc<Answer>>,
    waiters: Vec<Rc<Waiter>>,
}

struct Generator {
    query: usize,
    cursor: usize,
    depth: usize,
}

enum Progress {
    Continue,
    Finished(SearchResult),
    Unsupported,
}

#[derive(Default)]
struct Search {
    queries: Vec<Query>,
    keys: HashMap<Expr, Vec<(table::Key, usize)>>,
    generators: Vec<Generator>,
    resumes: Vec<(Rc<Waiter>, Rc<Answer>)>,
    attempts: usize,
    events: usize,
    key_units: usize,
}

fn restore(context: &mut Context, saved: &Context) {
    let spent = context.txn.budget.heartbeats_consumed;
    *context = saved.clone();
    context.txn.budget.heartbeats_consumed = spent;
}

impl Search {
    fn event(&mut self, context: &mut Context) -> Result<(), NatDefinitionElabError> {
        context.tick()?;
        self.events += 1;
        if self.events > MAX_TABLE_EVENTS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        Ok(())
    }

    fn query(
        &mut self,
        context: &mut Context,
        frame: Rc<Frame>,
        key: table::Key,
        depth: usize,
    ) -> Result<Option<usize>, NatDefinitionElabError> {
        if let Some(bucket) = self.keys.get(key.bucket()) {
            for (stored, index) in bucket {
                context.tick()?;
                if *stored == key {
                    return Ok(Some(*index));
                }
            }
        }
        if depth >= MAX_SEARCH_DEPTH || self.queries.len() >= MAX_CANDIDATE_ATTEMPTS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        if key.units() > MAX_TABLE_KEY_UNITS.saturating_sub(self.key_units) {
            return Ok(None);
        }
        self.event(context)?;
        self.key_units += key.units();
        let index = self.queries.len();
        self.keys
            .entry(key.bucket().clone())
            .or_default()
            .push((key, index));
        self.queries.push(Query {
            frame,
            answers: Vec::new(),
            waiters: Vec::new(),
        });
        self.generators.push(Generator {
            query: index,
            cursor: 0,
            depth,
        });
        Ok(Some(index))
    }

    fn consume(
        &mut self,
        context: &mut Context,
        mut consumer: Consumer,
        registry: &InstanceRegistry,
        ambient: &LocalContext,
    ) -> Result<Progress, NatDefinitionElabError> {
        let mut remaining = false;
        for goal in &consumer.subgoals {
            context.tick()?;
            if context.txn.mvars.is_assigned(goal) {
                continue;
            }
            remaining = true;
            let mut trial = context.clone();
            let child = trial.instance_frame(goal.clone(), registry, ambient, None, false);
            context.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
            let Some(child) = child? else {
                continue;
            };
            *context = trial;
            let Some(key) = table::shared_key(context, &child, false)? else {
                return Ok(Progress::Unsupported);
            };
            let child = Rc::new(child);
            let Some(query) = self.query(context, Rc::clone(&child), key, consumer.depth + 1)?
            else {
                return Ok(Progress::Unsupported);
            };
            consumer.context = context.clone();
            let waiter = Rc::new(Waiter {
                consumer: Rc::new(consumer),
                goal: child,
            });
            self.event(context)?;
            // Existing answers are pushed in discovery order. The last one
            // resumes first, exactly as a consumer of a pinned table entry.
            let answers = self.queries[query].answers.clone();
            for answer in answers {
                self.event(context)?;
                self.resumes.push((Rc::clone(&waiter), answer));
            }
            self.queries[query].waiters.push(waiter);
            return Ok(Progress::Continue);
        }
        if remaining {
            // The complete candidate has not determined any ready input.
            return Ok(Progress::Continue);
        }
        if consumer.size >= context.instance_max_result_size() {
            return Ok(Progress::Continue);
        }

        let frame = Rc::clone(&self.queries[consumer.query].frame);
        let value = context.instantiate(&consumer.value)?;
        // The selected dictionary can retain a reducible alias that its
        // requested target unfolded during matching. The pin deduplicates by
        // the dictionary's inferred type, so the target is not a substitute.
        let Some(actual) = context.known_type(&value)? else {
            return Ok(Progress::Unsupported);
        };
        let actual = context.instantiate(&actual)?;
        if value.has_expr_mvar()
            || value.has_level_mvar()
            || actual.has_expr_mvar()
            || actual.has_level_mvar()
        {
            // Replaying a non-ground answer requires abstracting its complete
            // metavariable graph. Leave that fragment to the existing search.
            return Ok(Progress::Unsupported);
        }
        context.txn.lctx = frame.base.txn.lctx.clone();
        let expected = context.instantiate(&frame.expected)?;
        match context.reconcile_instance_outputs(&frame, actual.clone(), expected) {
            Ok(()) => {}
            Err(error) if nonmatch(&error) => {
                // In particular, a selected outer outParam mismatch must not
                // be rescued by a lower-priority generator candidate.
                return Ok(if consumer.query == 0 {
                    Progress::Finished(SearchResult::Failed)
                } else {
                    Progress::Continue
                });
            }
            Err(error) => return Err(error),
        }
        let value = context.instantiate(&value)?;
        if consumer.query == 0 {
            context.assign_instance_answer(&frame, value)?;
            return Ok(Progress::Finished(SearchResult::Solved));
        }

        // The pin deduplicates completed answers by their instantiated type,
        // not by dictionary value; classes with fixed inputs are canonical.
        for answer in &self.queries[consumer.query].answers {
            context.tick()?;
            if answer.type_ == actual {
                return Ok(Progress::Continue);
            }
        }
        self.event(context)?;
        let answer = Rc::new(Answer {
            value,
            type_: actual,
            size: consumer.size.saturating_add(1),
        });
        self.queries[consumer.query]
            .answers
            .push(Rc::clone(&answer));
        let waiters = self.queries[consumer.query].waiters.clone();
        for waiter in waiters {
            self.event(context)?;
            self.resumes.push((waiter, Rc::clone(&answer)));
        }
        Ok(Progress::Continue)
    }

    fn step(
        &mut self,
        context: &mut Context,
        registry: &InstanceRegistry,
        ambient: &LocalContext,
    ) -> Result<Progress, NatDefinitionElabError> {
        if let Some((waiter, answer)) = self.resumes.pop() {
            restore(context, &waiter.consumer.context);
            if !table::replay_outputs(context, &waiter.goal, &answer.type_)? {
                return Ok(Progress::Continue);
            }
            context.assign_instance_answer(&waiter.goal, answer.value.clone())?;
            return self.consume(
                context,
                Consumer {
                    query: waiter.consumer.query,
                    context: context.clone(),
                    value: waiter.consumer.value.clone(),
                    subgoals: waiter.consumer.subgoals.clone(),
                    depth: waiter.consumer.depth,
                    size: waiter.consumer.size.saturating_add(answer.size),
                },
                registry,
                ambient,
            );
        }

        let Some(generator) = self.generators.last_mut() else {
            return Ok(Progress::Finished(SearchResult::Failed));
        };
        let query = generator.query;
        let depth = generator.depth;
        let frame = Rc::clone(&self.queries[query].frame);
        if !frame.resumable && !self.queries[query].answers.is_empty() {
            self.generators.pop();
            return Ok(Progress::Continue);
        }
        let Some(candidate) = frame.candidates.get(generator.cursor).cloned() else {
            self.generators.pop();
            return Ok(Progress::Continue);
        };
        generator.cursor += 1;
        self.attempts += 1;
        if self.attempts > MAX_CANDIDATE_ATTEMPTS {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        restore(context, &frame.base);
        let expansion = match context.expand_instance(&candidate, &frame.target, false, registry) {
            Ok(Some(expansion)) => expansion,
            Ok(None) => return Ok(Progress::Continue),
            Err(error) if nonmatch(&error) => return Ok(Progress::Continue),
            Err(error) => return Err(error),
        };
        self.consume(
            context,
            Consumer {
                query,
                context: context.clone(),
                value: expansion.value,
                subgoals: expansion.subgoals,
                depth,
                size: 0,
            },
            registry,
            ambient,
        )
    }
}

impl Context {
    pub(super) fn search_instances_tabled(
        &mut self,
        root: MVarId,
        registry: &InstanceRegistry,
    ) -> Result<Option<SearchResult>, NatDefinitionElabError> {
        let ambient = self
            .txn
            .mvars
            .get_decl(&root)
            .ok_or_else(|| failure(SourceInferenceError::Scope))?
            .lctx
            .clone();
        let Some(first) = self.instance_frame(root, registry, &ambient, None, true)? else {
            return Ok(Some(SearchResult::Stuck));
        };
        let Some(key) = table::shared_key(self, &first, true)? else {
            return Ok(None);
        };
        let mut search = Search::default();
        if search.query(self, Rc::new(first), key, 0)?.is_none() {
            return Ok(None);
        }
        loop {
            self.tick()?;
            match search.step(self, registry, &ambient)? {
                Progress::Continue => {}
                Progress::Finished(result) => return Ok(Some(result)),
                Progress::Unsupported => return Ok(None),
            }
        }
    }
}
