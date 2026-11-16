//! Read-only Lean RPC goal and diagnostic procedures with bounded document-local sessions.
//! Pinned contracts: Lean/Data/Lsp/Extra.lean and Lean/Server/Rpc/Basic.lean.
//! The retained objects are immutable native presentations. They are not proof
//! certificates or executable Meta contexts; unimplemented procedures refuse.
use super::*;
use json::rpc::{self as params, WireFormat};
use semantic::{Answer, Code, ExpressionInfo, Query, QueryKind};
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
fn highlight_error(error: params::highlight::Error) -> (i32, String) {
    match error {
        params::highlight::Error::Invalid(message) => invalid(message),
        params::highlight::Error::Unsupported(message)
        | params::highlight::Error::Limit(message) => failed(message),
    }
}

struct Snapshot {
    version: i64,
    offset: usize,
    answer: Answer,
    bytes: usize,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum CodeField {
    Target,
    HypothesisType(usize),
    HypothesisValue(usize),
}
#[derive(Clone, Copy, PartialEq, Eq)]
struct CodeAddress {
    goal: usize,
    field: CodeField,
}
#[derive(Clone, Copy, PartialEq, Eq)]
struct InfoAddress {
    code: CodeAddress,
    subexpression: Option<usize>,
}
impl Snapshot {
    fn code(&self, address: CodeAddress) -> Option<&Code> {
        let (hypotheses, target) = match &self.answer {
            Answer::InteractiveGoals { goals } => {
                let goal = goals.get(address.goal)?;
                (&goal.hypotheses, &goal.target)
            }
            Answer::InteractiveTermGoal(goal) if address.goal == 0 => {
                (&goal.hypotheses, &goal.target)
            }
            _ => return None,
        };
        match address.field {
            CodeField::Target => Some(target),
            CodeField::HypothesisType(index) => Some(&hypotheses.get(index)?.type_),
            CodeField::HypothesisValue(index) => hypotheses.get(index)?.value.as_ref(),
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum ReferenceKind {
    Context,
    Term,
    Info(InfoAddress),
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
        // Every reference shares the same immutable answer. Charge its payload
        // once, plus one bounded metadata row per distinct reference. A goal
        // with many expression tags must not be charged as many full snapshots.
        let payload = if self
            .references
            .values()
            .any(|reference| Arc::ptr_eq(&reference.snapshot, snapshot))
        {
            0
        } else {
            snapshot.bytes
        };
        let bytes = payload
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
                bytes: 128,
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
            if !self
                .references
                .values()
                .any(|other| Arc::ptr_eq(&other.snapshot, &reference.snapshot))
            {
                self.bytes -= reference.snapshot.bytes;
            }
        }
    }

    fn retain_expression(&mut self, id: u64) -> Result<()> {
        // Decoding an InfoWithCtx requires an existing expression reference,
        // not a goal context, a client-invented identity or a released snapshot.
        self.expression(id)?;
        let reference = self
            .references
            .get_mut(&id)
            .ok_or_else(|| invalid("RPC expression reference is unknown or has been released"))?;
        reference.count = reference
            .count
            .checked_add(1)
            .ok_or_else(|| failed("RPC reference count exhausted"))?;
        Ok(())
    }

    fn expression(&self, id: u64) -> Result<(&str, &ExpressionInfo)> {
        let reference = self
            .references
            .get(&id)
            .ok_or_else(|| invalid("RPC expression reference is unknown or has been released"))?;
        let ReferenceKind::Info(address) = reference.kind else {
            return Err(invalid(
                "RPC reference does not contain expression information",
            ));
        };
        let code = reference
            .snapshot
            .code(address.code)
            .ok_or_else(|| failed("retained RPC expression is unavailable"))?;
        let (expression, info) = match address.subexpression {
            None => (
                code.text.as_str(),
                code.info
                    .as_ref()
                    .ok_or_else(|| failed("retained RPC expression has no information"))?,
            ),
            Some(index) => {
                let subexpression = code
                    .subexpressions
                    .get(index)
                    .ok_or_else(|| failed("retained RPC subexpression is unavailable"))?;
                let expression = code
                    .text
                    .get(subexpression.range.clone())
                    .ok_or_else(|| failed("retained RPC expression range is invalid"))?;
                (expression, &subexpression.info)
            }
        };
        Ok((expression, info))
    }

    fn popup(&self, id: u64) -> Result<String> {
        let (expression, info) = self.expression(id)?;
        Ok(popup_json(expression, info))
    }

    fn interactive_message(&self, id: u64, _indent: usize) -> Result<String> {
        // Native diagnostics emit plain `TaggedText` (`{"text":...}`) directly
        // without allocating opaque `MessageData` RPC references. An unknown ID
        // is refused as an invalid reference; an existing goal/expression ID is
        // refused as a `WithRpcRef` type mismatch, matching `Lean.Server.Rpc`.
        if self.references.contains_key(&id) {
            Err(invalid(&format!(
                "RPC call type mismatch in reference '{id}': expected 'Lean.MessageData'"
            )))
        } else {
            Err(invalid(&format!("RPC reference '{id}' is not valid")))
        }
    }

    fn lazy_trace_children(&self, id: u64) -> Result<String> {
        if self.references.contains_key(&id) {
            Err(invalid(&format!(
                "RPC call type mismatch in reference '{id}': expected 'Lean.Widget.LazyTraceChildren'"
            )))
        } else {
            Err(invalid(&format!("RPC reference '{id}' is not valid")))
        }
    }

    fn go_to(&self, id: u64, kind: params::GoToKind) -> Result<String> {
        let (_, info) = self.expression(id)?;
        let locations = match kind {
            params::GoToKind::Declaration | params::GoToKind::Definition => &info.definition,
            params::GoToKind::Type => &info.type_definition,
        }
        .as_ref()
        .ok_or_else(|| failed("source navigation is unavailable for this retained expression"))?;
        Ok(format!(
            "[{}]",
            locations
                .iter()
                .map(semantic::NavigationLocation::wire)
                .collect::<Vec<_>>()
                .join(",")
        ))
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
        if call.method == "Lean.Widget.InteractiveDiagnostics.infoToInteractive" {
            let reference = params::reference(call.params, self.format).map_err(invalid)?;
            let result = self
                .session(call.session, &call.uri, Instant::now())?
                .popup(reference)?;
            if result.len() > MAX_RESPONSE_BYTES {
                return Err(failed("RPC popup exceeds its wire budget"));
            }
            self.session(call.session, &call.uri, Instant::now())?;
            return Ok(result);
        }
        if call.method == "Lean.Widget.getGoToLocation" {
            let (kind, reference) = params::go_to(call.params, self.format).map_err(invalid)?;
            let result = self
                .session(call.session, &call.uri, Instant::now())?
                .go_to(reference, kind)?;
            if result.len() > MAX_RESPONSE_BYTES {
                return Err(failed("RPC navigation exceeds its wire budget"));
            }
            self.session(call.session, &call.uri, Instant::now())?;
            return Ok(result);
        }
        if call.method == "Lean.Widget.highlightMatches" {
            // Search the presentation already held by the client. This is not
            // another semantic query. Re-encoding an expression retains its
            // existing InfoWithCtx once per occurrence, so releasing the input
            // cannot invalidate a hover in the highlighted presentation.
            let request = params::highlight::Request::decode(call.params, self.format)
                .map_err(highlight_error)?;
            let mut staged = self
                .session(call.session, &call.uri, Instant::now())?
                .clone();
            for reference in request.references() {
                staged.retain_expression(reference)?;
            }
            let result = request
                .response(MAX_RESPONSE_BYTES)
                .map_err(highlight_error)?;
            // Invalid later references, output exhaustion and session expiry
            // publish neither a partial result nor partial reference counts.
            *self.session(call.session, &call.uri, Instant::now())? = staged;
            return Ok(result);
        }
        if call.method == "Lean.Widget.getWidgets" {
            // Pinned contract (`Lean/Widget/UserWidget.lean:283-315`): `getWidgets`
            // decodes a bare `Lean.Lsp.Position` and returns `GetWidgetsResponse`
            // (`{"widgets":[]}` when no panel widgets are registered at that
            // position). Validate the UTF-16 position against the current source
            // without fabricating widgets or expression references.
            let position = params::widget_position(call.params).map_err(invalid)?;
            json::byte_offset(text, position).map_err(invalid)?;
            self.session(call.session, &call.uri, Instant::now())?;
            return Ok("{\"widgets\":[]}".to_owned());
        }
        if call.method == "Lean.Widget.getWidgetSource" {
            // Pinned contract (`Lean/Widget/UserWidget.lean:95-124`): `getWidgetSource`
            // decodes `{ hash : UInt64, pos : Lean.Lsp.Position }`, validates `pos`
            // against the open document, and refuses unregistered hashes with `-32602`
            // (`"No widget module with hash <hash> registered"`).
            let (hash, position) = params::widget_source(call.params).map_err(invalid)?;
            json::byte_offset(text, position).map_err(invalid)?;
            self.session(call.session, &call.uri, Instant::now())?;
            return Err(invalid(&format!(
                "No widget module with hash {hash} registered"
            )));
        }
        if call.method == "Lean.Widget.InteractiveDiagnostics.msgToInteractive" {
            let (reference, indent) =
                params::msg_to_interactive(call.params, self.format).map_err(invalid)?;
            let result = self
                .session(call.session, &call.uri, Instant::now())?
                .interactive_message(reference, indent)?;
            self.session(call.session, &call.uri, Instant::now())?;
            return Ok(result);
        }
        if call.method == "Lean.Widget.lazyTraceChildrenToInteractive" {
            let reference = params::reference(call.params, self.format).map_err(invalid)?;
            let result = self
                .session(call.session, &call.uri, Instant::now())?
                .lazy_trace_children(reference)?;
            self.session(call.session, &call.uri, Instant::now())?;
            return Ok(result);
        }
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
        let bytes = semantic::interactive::validate(&answer, query).map_err(failed)?;
        let snapshot = Arc::new(Snapshot {
            version: query.version,
            offset,
            answer,
            bytes,
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

fn popup_json(expression: &str, info: &ExpressionInfo) -> String {
    let type_ = info
        .type_
        .as_ref()
        .map_or_else(|| "null".to_owned(), |type_| code(type_));
    format!(
        "{{\"exprExplicit\":{},\"type\":{type_},\"doc\":null}}",
        code(expression)
    )
}

fn tagged(reference: &str, mut position: u64, contents: &str) -> String {
    // Lean/SubExpr.lean encodes the path as a string because a bare Nat loses
    // low bits when JavaScript decodes it as a float.
    let mut coordinates = Vec::new();
    while position >= 4 {
        coordinates.push((b'0' + (position % 4) as u8) as char);
        position /= 4;
    }
    let mut path = String::new();
    if coordinates.is_empty() {
        path.push('/');
    } else {
        for coordinate in coordinates.into_iter().rev() {
            path.push('/');
            path.push(coordinate);
        }
    }
    format!(
        "{{\"tag\":[{{\"info\":{reference},\"subexprPos\":{}}},{contents}]}}",
        crate::json_string(&path)
    )
}

fn interactive_code(
    snapshot: &Arc<Snapshot>,
    address: CodeAddress,
    session: &mut Session,
    format: WireFormat,
) -> Result<String> {
    let value = snapshot
        .code(address)
        .ok_or_else(|| failed("RPC expression address is unavailable"))?;
    let mut parts = Vec::new();
    let mut offset = 0;
    for (index, subexpression) in value.subexpressions.iter().enumerate() {
        if subexpression.range.start > offset {
            parts.push(code(&value.text[offset..subexpression.range.start]));
        }
        let reference = format.reference(session.retain(
            snapshot,
            ReferenceKind::Info(InfoAddress {
                code: address,
                subexpression: Some(index),
            }),
        )?);
        parts.push(tagged(
            &reference,
            subexpression.position,
            &code(&value.text[subexpression.range.clone()]),
        ));
        offset = subexpression.range.end;
    }
    if offset < value.text.len() || parts.is_empty() {
        parts.push(code(&value.text[offset..]));
    }
    let contents = if parts.len() == 1 {
        parts
            .pop()
            .ok_or_else(|| failed("RPC expression encoding has no content"))?
    } else {
        format!("{{\"append\":[{}]}}", parts.join(","))
    };
    if value.info.is_some() {
        let reference = format.reference(session.retain(
            snapshot,
            ReferenceKind::Info(InfoAddress {
                code: address,
                subexpression: None,
            }),
        )?);
        Ok(tagged(&reference, 1, &contents))
    } else {
        Ok(contents)
    }
}

fn goal_core(
    snapshot: &Arc<Snapshot>,
    goal: usize,
    session: &mut Session,
    format: WireFormat,
) -> Result<String> {
    let hyps = match &snapshot.answer {
        Answer::InteractiveGoals { goals } => &goals[goal].hypotheses,
        Answer::InteractiveTermGoal(goal) => &goal.hypotheses,
        _ => return Err(failed("RPC snapshot is not a goal")),
    };
    let mut hypotheses = Vec::new();
    for (index, hyp) in hyps.iter().enumerate() {
        let type_ = interactive_code(
            snapshot,
            CodeAddress {
                goal,
                field: CodeField::HypothesisType(index),
            },
            session,
            format,
        )?;
        let value = if hyp.value.is_some() {
            format!(
                ",\"val\":{}",
                interactive_code(
                    snapshot,
                    CodeAddress {
                        goal,
                        field: CodeField::HypothesisValue(index),
                    },
                    session,
                    format,
                )?
            )
        } else {
            String::new()
        };
        hypotheses.push(format!(
            "{{\"names\":[{}],\"fvarIds\":[{}],\"type\":{type_}{value}}}",
            crate::json_string(&hyp.name),
            crate::json_string(&hyp.fvar_id),
        ));
    }
    let target = interactive_code(
        snapshot,
        CodeAddress {
            goal,
            field: CodeField::Target,
        },
        session,
        format,
    )?;
    Ok(format!(
        "\"hyps\":[{}],\"type\":{target}",
        hypotheses.join(",")
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
            for (index, goal) in goals.iter().enumerate() {
                let context = format.reference(session.retain(snapshot, ReferenceKind::Context)?);
                let core = goal_core(snapshot, index, session, format)?;
                let name = goal.user_name.as_ref().map_or(String::new(), |name| {
                    format!(",\"userName\":{}", crate::json_string(name))
                });
                result.push(format!(
                    "{{{core},\"ctx\":{context},\"goalPrefix\":\"⊢ \",\"mvarId\":{}{name}}}",
                    crate::json_string(&goal.mvar_id)
                ));
            }
            Ok(format!("{{\"goals\":[{}]}}", result.join(",")))
        }
        Answer::InteractiveTermGoal(goal) => {
            let context = format.reference(session.retain(snapshot, ReferenceKind::Context)?);
            let term = format.reference(session.retain(snapshot, ReferenceKind::Term)?);
            let core = goal_core(snapshot, 0, session, format)?;
            let start = semantic::position(query.text, goal.range.start).map_err(failed)?;
            let end = semantic::position(query.text, goal.range.end).map_err(failed)?;
            Ok(format!(
                "{{{core},\"ctx\":{context},\"term\":{term},\"range\":{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}}}",
                start.line, start.character, end.line, end.character
            ))
        }
        _ => Err(failed("cannot encode this RPC result kind")),
    }
}
