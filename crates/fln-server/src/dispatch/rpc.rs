//! Read-only Lean RPC goal and diagnostic procedures with bounded document-local sessions.
//! Pinned contracts: Lean/Data/Lsp/Extra.lean and Lean/Server/Rpc/Basic.lean.
//! The retained objects are immutable native presentations. They are not proof
//! certificates or executable Meta contexts; unimplemented procedures refuse.
use super::*;
use json::rpc::{self as params, WireFormat};
use semantic::{Answer, Goal, Hypothesis, Query, QueryKind, TermGoal};
use std::collections::hash_map::RandomState;
use std::hash::BuildHasher;
use std::sync::Arc;
use std::time::{Duration, Instant};

#[cfg(test)]
mod tests;
const KEEP_ALIVE: Duration = Duration::from_secs(30);
const MAX_SESSIONS: usize = 32;
const MAX_REFERENCES: usize = 4096;
const MAX_RETAINED_BYTES: usize = 4 * 1024 * 1024;
const MAX_RESPONSE_BYTES: usize = 1024 * 1024;
const RECONNECT: i32 = -32900;
type Result<T> = std::result::Result<T, (i32, String)>;
fn invalid(message: &str) -> (i32, String) {
    (-32602, message.to_owned())
}
fn failed(message: &str) -> (i32, String) {
    (REQUEST_FAILED_CODE, message.to_owned())
}
fn outdated() -> (i32, String) {
    (RECONNECT, "Outdated RPC session".to_owned())
}

struct Snapshot {
    version: i64,
    offset: usize,
    answer: Answer,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum ReferenceKind {
    Context,
    Term,
}
#[derive(Clone)]
struct Reference {
    snapshot: Arc<Snapshot>,
    kind: ReferenceKind,
    count: usize,
    bytes: usize,
}
#[derive(Clone)]
struct Session {
    uri: String,
    expires: Instant,
    next_reference: u64,
    references: BTreeMap<u64, Reference>,
    bytes: usize,
}
impl Session {
    fn retain(&mut self, snapshot: &Arc<Snapshot>, kind: ReferenceKind) -> Result<u64> {
        if let Some((id, reference)) = self.references.iter_mut().find(|(_, reference)| {
            reference.kind == kind
                && Arc::ptr_eq(&reference.snapshot, snapshot)
                && reference.snapshot.version == snapshot.version
                && reference.snapshot.offset == snapshot.offset
        }) {
            reference.count = reference
                .count
                .checked_add(1)
                .ok_or_else(|| failed("RPC reference count exhausted"))?;
            return Ok(*id);
        }
        if self.references.len() >= MAX_REFERENCES {
            return Err(failed("RPC reference capacity exhausted"));
        }
        let bytes = semantic::interactive::payload_bytes(&snapshot.answer)
            .map_err(failed)?
            .checked_add(128)
            .ok_or_else(|| failed("RPC reference accounting overflow"))?;
        let total = self
            .bytes
            .checked_add(bytes)
            .filter(|n| *n <= MAX_RETAINED_BYTES)
            .ok_or_else(|| failed("RPC retained snapshot budget exhausted"))?;
        let id = self.next_reference;
        self.next_reference = id
            .checked_add(1)
            .ok_or_else(|| failed("RPC reference identities exhausted"))?;
        self.references.insert(
            id,
            Reference {
                snapshot: snapshot.clone(),
                kind,
                count: 1,
                bytes,
            },
        );
        self.bytes = total;
        Ok(id)
    }
    fn release(&mut self, id: u64) {
        let Some(reference) = self.references.get_mut(&id) else {
            return;
        };
        if reference.count > 1 {
            reference.count -= 1;
        } else if let Some(reference) = self.references.remove(&id) {
            self.bytes -= reference.bytes;
        }
    }
}

pub(super) struct Sessions {
    format: WireFormat,
    nonce: u64,
    next_session: u64,
    sessions: BTreeMap<u64, Session>,
}
impl Default for Sessions {
    fn default() -> Self {
        Self {
            format: WireFormat::default(),
            nonce: RandomState::new().hash_one(std::process::id()),
            next_session: 0,
            sessions: BTreeMap::new(),
        }
    }
}
impl Sessions {
    pub(super) fn configure(
        &mut self,
        value: RawField<'_>,
    ) -> std::result::Result<(), &'static str> {
        self.format = params::wire_format(value)?;
        Ok(())
    }
    pub(super) fn sweep(&mut self, now: Instant) {
        self.sessions.retain(|_, session| session.expires > now);
    }
    pub(super) fn clear(&mut self) {
        self.sessions.clear();
    }
    pub(super) fn close(&mut self, uri: &str) {
        self.sessions.retain(|_, session| session.uri != uri);
    }
    fn create(&mut self, uri: String, now: Instant) -> Result<u64> {
        self.sweep(now);
        if self.sessions.len() >= MAX_SESSIONS {
            return Err(failed("RPC session capacity exhausted"));
        }
        let next = self
            .next_session
            .checked_add(1)
            .ok_or_else(|| failed("RPC session identities exhausted"))?;
        let expires = now
            .checked_add(KEEP_ALIVE)
            .ok_or_else(|| failed("RPC session clock overflow"))?;
        // Addition is a permutation of u64. The checked sequence never repeats,
        // while the randomly seeded base keeps IDs distinct across server starts.
        let id = self.nonce.wrapping_add(self.next_session);
        self.next_session = next;
        self.sessions.insert(
            id,
            Session {
                uri,
                expires,
                next_reference: 0,
                references: BTreeMap::new(),
                bytes: 0,
            },
        );
        Ok(id)
    }
    fn session(&mut self, id: u64, uri: &str, now: Instant) -> Result<&mut Session> {
        self.sweep(now);
        self.sessions
            .get_mut(&id)
            .filter(|session| session.uri == uri)
            .ok_or_else(outdated)
    }
    pub(super) fn notify(&mut self, method: &str, value: RawField<'_>) -> Result<()> {
        let (uri, id) = params::notification(value).map_err(invalid)?;
        // Validate the complete batch before releasing even its first reference.
        let references = if method == "$/lean/rpc/release" {
            params::references(value, self.format).map_err(invalid)?
        } else {
            Vec::new()
        };
        let now = Instant::now();
        let session = self.session(id, &uri, now)?;
        for id in references {
            session.release(id);
        }
        session.expires = now
            .checked_add(KEEP_ALIVE)
            .ok_or_else(|| failed("RPC session clock overflow"))?;
        Ok(())
    }
    pub(super) fn request(
        &mut self,
        method: &str,
        value: RawField<'_>,
        id: &RequestId,
        documents: &DocumentSession,
        checker: &mut dyn CheckSource,
    ) -> String {
        let result = if checker.semantic_queries() {
            self.execute(method, value, documents, checker)
        } else {
            Err(failed("Lean RPC requires a native semantic query provider"))
        };
        match result {
            Ok(result) => format!(
                "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{result}}}",
                id.as_json()
            ),
            Err((code, message)) => {
                let detail = if message.len() <= 16 * 1024 {
                    &message
                } else {
                    "RPC failed (provider detail exceeded its output limit)"
                };
                error_response(id, code, detail)
            }
        }
    }
    fn execute(
        &mut self,
        method: &str,
        value: RawField<'_>,
        documents: &DocumentSession,
        checker: &mut dyn CheckSource,
    ) -> Result<String> {
        let sources = documents.sources();
        if method == "$/lean/rpc/connect" {
            let uri = params::connect(value).map_err(invalid)?;
            if !sources.iter().any(|source| source.uri == uri) {
                return Err(failed("RPC document is not open"));
            }
            let id = self.create(uri, Instant::now())?;
            return Ok(format!("{{\"sessionId\":\"{id}\"}}"));
        }
        let call = params::call(value).map_err(invalid)?;
        self.session(call.session, &call.uri, Instant::now())?;
        let document = sources
            .iter()
            .find(|source| source.uri == call.uri)
            .ok_or_else(outdated)?;
        let text = document
            .text
            .ok_or_else(|| failed("accepted editor source is unavailable"))?;
        if call.method == "Lean.Widget.getInteractiveDiagnostics" {
            // Unlike goals, this procedure takes only an optional lineRange.
            // Read the latest completed native check, not a new elaboration at
            // the cursor, and do not allocate fictitious expression references.
            let range = params::diagnostics::line_range(call.params).map_err(invalid)?;
            let result = checker
                .diagnostics(&call.uri, document.version)
                .map_err(failed)?
                .response(range, MAX_RESPONSE_BYTES)
                .map_err(failed)?;
            self.session(call.session, &call.uri, Instant::now())?;
            return Ok(result);
        }
        json::byte_offset(text, call.position).map_err(invalid)?;
        let kind = match call.method.as_str() {
            "Lean.Widget.getInteractiveGoals" => QueryKind::InteractiveGoals,
            "Lean.Widget.getInteractiveTermGoal" => QueryKind::InteractiveTermGoal,
            _ => {
                return Err((
                    -32601,
                    format!("RPC procedure `{}` is not implemented", call.method),
                ));
            }
        };
        let position = params::goal_position(call.params, &call.uri).map_err(invalid)?;
        let offset = json::byte_offset(text, position).map_err(invalid)?;
        let query = Query {
            kind,
            uri: &call.uri,
            version: document.version,
            text,
            offset,
        };
        let answer = checker
            .query(query, &sources)
            .map_err(|message| (REQUEST_FAILED_CODE, message))?;
        // A slow native inspection must not resurrect an expired session.
        self.session(call.session, &call.uri, Instant::now())?;
        let Some(answer) = answer else {
            return Ok("null".to_owned());
        };
        if !matches!(
            (kind, &answer),
            (QueryKind::InteractiveGoals, Answer::InteractiveGoals { .. })
                | (
                    QueryKind::InteractiveTermGoal,
                    Answer::InteractiveTermGoal(_)
                )
        ) {
            return Err(failed("RPC provider returned a different query kind"));
        }
        semantic::interactive::validate(&answer, query).map_err(failed)?;
        let snapshot = Arc::new(Snapshot {
            version: query.version,
            offset,
            answer,
        });
        // Stage bounded reference metadata. Incomplete encoding or exhaustion
        // cannot leak partial objects or reuse a number already sent to a client.
        let mut staged = self
            .session(call.session, &call.uri, Instant::now())?
            .clone();
        let result = encode(&snapshot, &mut staged, self.format, query)?;
        if result.len() > MAX_RESPONSE_BYTES {
            return Err(failed("RPC response exceeds its wire budget"));
        }
        *self.session(call.session, &call.uri, Instant::now())? = staged;
        Ok(result)
    }
}

fn code(text: &str) -> String {
    format!("{{\"text\":{}}}", crate::json_string(text))
}
fn hypotheses(hyps: &[Hypothesis]) -> String {
    hyps.iter()
        .map(|hyp| {
            let value = hyp
                .value
                .as_ref()
                .map_or(String::new(), |value| format!(",\"val\":{}", code(value)));
            format!(
                "{{\"names\":[{}],\"fvarIds\":[{}],\"type\":{}{value}}}",
                crate::json_string(&hyp.name),
                crate::json_string(&hyp.fvar_id),
                code(&hyp.type_)
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}
fn goal_json(goal: &Goal, context: &str) -> String {
    let name = goal.user_name.as_ref().map_or(String::new(), |name| {
        format!(",\"userName\":{}", crate::json_string(name))
    });
    format!(
        "{{\"hyps\":[{}],\"type\":{},\"ctx\":{context},\"goalPrefix\":\"⊢ \",\"mvarId\":{}{name}}}",
        hypotheses(&goal.hypotheses),
        code(&goal.target),
        crate::json_string(&goal.mvar_id)
    )
}
fn term_json(goal: &TermGoal, context: &str, term: &str, query: Query<'_>) -> Result<String> {
    let start = semantic::position(query.text, goal.range.start).map_err(failed)?;
    let end = semantic::position(query.text, goal.range.end).map_err(failed)?;
    Ok(format!(
        "{{\"hyps\":[{}],\"type\":{},\"ctx\":{context},\"term\":{term},\"range\":{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}}}",
        hypotheses(&goal.hypotheses),
        code(&goal.target),
        start.line,
        start.character,
        end.line,
        end.character
    ))
}
fn encode(
    snapshot: &Arc<Snapshot>,
    session: &mut Session,
    format: WireFormat,
    query: Query<'_>,
) -> Result<String> {
    match &snapshot.answer {
        Answer::InteractiveGoals { goals } => {
            let mut result = Vec::new();
            for goal in goals {
                let context = format.reference(session.retain(snapshot, ReferenceKind::Context)?);
                result.push(goal_json(goal, &context));
            }
            Ok(format!("{{\"goals\":[{}]}}", result.join(",")))
        }
        Answer::InteractiveTermGoal(goal) => {
            let context = format.reference(session.retain(snapshot, ReferenceKind::Context)?);
            let term = format.reference(session.retain(snapshot, ReferenceKind::Term)?);
            term_json(goal, &context, &term, query)
        }
        _ => Err(failed("cannot encode this RPC result kind")),
    }
}
