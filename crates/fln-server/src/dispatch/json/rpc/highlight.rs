//! Literal search over interactive diagnostic presentations and expressions.
//! Contract: Lean/Server/FileWorker/WidgetRequests.lean,
//! `highlightTaggedText` and `highlightStringMatches?` at the locked Reference.
//!
//! Keep the original append tree: matches can cross text nodes, and the pin's
//! treatment of overlapping matches is node-sensitive. Flattening the result
//! or replacing KMP by non-overlapping `str::match_indices` changes that wire
//! behavior. Expression tags are decoded and re-encoded structurally; the caller
//! validates and retains their live InfoWithCtx references before publishing.
//! Goals, widgets and traces still require their own retained object contracts.
use super::*;
use std::ops::Range;

const MAX_INPUT_BYTES: usize = 1024 * 1024;
const MAX_QUERY_BYTES: usize = 16 * 1024;
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 64;
const MAX_MATCHES: usize = 65536;
const MAX_PARSE_BYTES: usize = 16 * MAX_INPUT_BYTES;

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::dispatch) enum Error {
    Invalid(&'static str),
    Unsupported(&'static str),
    Limit(&'static str),
}

fn push<T>(values: &mut Vec<T>, value: T, limit: usize) -> Result<()> {
    if values.len() >= limit {
        return Err(Error::Limit(
            "RPC highlight working table exceeds its limit",
        ));
    }
    values
        .try_reserve(1)
        .map_err(|_| Error::Limit("RPC highlight allocation failed"))?;
    values.push(value);
    Ok(())
}

struct SubexprInfo {
    reference: u64,
    position: String,
    diff_status: Option<&'static str>,
}

impl SubexprInfo {
    fn decode(raw: &str, format: WireFormat) -> Result<Self> {
        let raw = object(RawField::Value(raw)).map_err(Error::Invalid)?;
        let reference = reference(object_field(raw, "info"), format).map_err(Error::Invalid)?;
        let position = string(RawField::Value(raw), "subexprPos").map_err(Error::Invalid)?;
        // Lean.SubExpr.Pos uses slash-separated base-four coordinates. It is a
        // Nat in Lean, so preserve long paths without narrowing them to u64.
        if position != "/"
            && (!position.starts_with('/')
                || !position[1..]
                    .split('/')
                    .all(|coordinate| matches!(coordinate, "0" | "1" | "2" | "3")))
        {
            return Err(Error::Invalid(
                "RPC highlight has an invalid subexpression position",
            ));
        }
        let diff_status = match object_field(raw, "diffStatus") {
            RawField::Missing | RawField::Value("null") => None,
            field => {
                let DecodedField::Valid(status) = decoded_string(field) else {
                    return Err(Error::Invalid(
                        "RPC highlight has an invalid expression diff status",
                    ));
                };
                Some(match status.as_str() {
                    "wasChanged" => "wasChanged",
                    "willChange" => "willChange",
                    "wasDeleted" => "wasDeleted",
                    "willDelete" => "willDelete",
                    "wasInserted" => "wasInserted",
                    "willInsert" => "willInsert",
                    _ => {
                        return Err(Error::Invalid(
                            "RPC highlight has an unknown expression diff status",
                        ));
                    }
                })
            }
        };
        Ok(Self {
            reference,
            position,
            diff_status,
        })
    }
}

#[derive(Clone, Copy)]
enum Tree {
    Message,
    Code,
}

// A flat arena avoids recursive traversal and recursive destruction of a
// client-supplied tagged tree. Text spans refer to one bounded UTF-8 buffer.
enum Node {
    Text(Range<usize>),
    Append(Vec<usize>),
    Expression { code: usize, child: usize },
    Info { info: SubexprInfo, child: usize },
}
struct Message {
    nodes: Vec<Node>,
    text: String,
    search_text: String,
    root: usize,
}

fn constructor(raw: &str) -> Result<(String, &str)> {
    let bytes = raw.as_bytes();
    let start = skip_ws(bytes, 0);
    let end = parse_value_end(raw, start, 0).ok_or(Error::Invalid(
        "RPC highlight message contains malformed JSON",
    ))?;
    if bytes.get(start) != Some(&b'{') || skip_ws(bytes, end) != bytes.len() {
        return Err(Error::Invalid(
            "RPC highlight message requires TaggedText objects",
        ));
    }
    let cursor = skip_ws(bytes, start + 1);
    let key_end = scan_string_end(bytes, cursor)
        .ok_or(Error::Invalid("RPC highlight message has no constructor"))?;
    let key = decode_json_string_value(&raw[cursor..key_end]).ok_or(Error::Invalid(
        "RPC highlight constructor is not a valid string",
    ))?;
    let cursor = skip_ws(bytes, key_end);
    if bytes.get(cursor) != Some(&b':') {
        return Err(Error::Invalid("RPC highlight constructor requires a value"));
    }
    let cursor = skip_ws(bytes, cursor + 1);
    let value_end = parse_value_end(raw, cursor, 0).ok_or(Error::Invalid(
        "RPC highlight constructor has a malformed value",
    ))?;
    let close = skip_ws(bytes, value_end);
    if bytes.get(close) != Some(&b'}') || skip_ws(bytes, close + 1) != bytes.len() {
        return Err(Error::Invalid(
            "RPC highlight message has ambiguous constructors",
        ));
    }
    Ok((key, &raw[cursor..value_end]))
}

fn children(raw: &str) -> Result<Vec<&str>> {
    let bytes = raw.as_bytes();
    if bytes.first() != Some(&b'[') {
        return Err(Error::Invalid(
            "RPC highlight constructor requires an array",
        ));
    }
    let mut cursor = skip_ws(bytes, 1);
    let mut result = Vec::new();
    if bytes.get(cursor) == Some(&b']') && skip_ws(bytes, cursor + 1) == bytes.len() {
        return Ok(result);
    }
    loop {
        let end = parse_value_end(raw, cursor, 0).ok_or(Error::Invalid(
            "RPC highlight constructor contains a malformed child",
        ))?;
        push(&mut result, &raw[cursor..end], MAX_NODES)?;
        cursor = skip_ws(bytes, end);
        match bytes.get(cursor) {
            Some(b']') if skip_ws(bytes, cursor + 1) == bytes.len() => return Ok(result),
            Some(b',') => cursor = skip_ws(bytes, cursor + 1),
            _ => {
                return Err(Error::Invalid(
                    "RPC highlight constructor array is malformed",
                ));
            }
        }
    }
}

impl Message {
    fn decode(raw: &str, format: WireFormat) -> Result<Self> {
        enum Work<'a> {
            Read(&'a str, usize, Tree, bool),
            Append(usize),
            Expression,
            Info(SubexprInfo),
        }
        let mut nodes = Vec::new();
        let mut text = String::new();
        let mut search_text = String::new();
        let mut work = Vec::new();
        let mut values = Vec::new();
        let mut visits = 0usize;
        let mut scanned = 0usize;
        push(
            &mut work,
            Work::Read(raw, 0, Tree::Message, true),
            2 * MAX_NODES,
        )?;
        while let Some(task) = work.pop() {
            match task {
                Work::Read(raw, depth, tree, searchable) => {
                    visits += 1;
                    if visits > MAX_NODES || depth > MAX_DEPTH {
                        return Err(Error::Limit("RPC highlight message exceeds its tree limit"));
                    }
                    scanned = scanned
                        .checked_add(raw.len())
                        .filter(|bytes| *bytes <= MAX_PARSE_BYTES)
                        .ok_or(Error::Limit("RPC highlight parsing exceeds its work limit"))?;
                    let (key, value) = constructor(raw)?;
                    match key.as_str() {
                        "text" => {
                            let value = decode_json_string_value(value).ok_or(Error::Invalid(
                                "RPC highlight text is not a valid string",
                            ))?;
                            let start = text.len();
                            let end = start
                                .checked_add(value.len())
                                .filter(|bytes| *bytes <= MAX_INPUT_BYTES)
                                .ok_or(Error::Limit("RPC highlight text exceeds its byte limit"))?;
                            text.try_reserve(value.len()).map_err(|_| {
                                Error::Limit("RPC highlight text allocation failed")
                            })?;
                            text.push_str(&value);
                            if searchable {
                                search_text.try_reserve(value.len()).map_err(|_| {
                                    Error::Limit("RPC highlight search text allocation failed")
                                })?;
                                search_text.push_str(&value);
                            }
                            let index = nodes.len();
                            push(&mut nodes, Node::Text(start..end), MAX_NODES)?;
                            push(&mut values, index, MAX_NODES)?;
                        }
                        "append" => {
                            let children = children(value)?;
                            push(&mut work, Work::Append(children.len()), 2 * MAX_NODES)?;
                            for child in children.into_iter().rev() {
                                push(
                                    &mut work,
                                    Work::Read(child, depth + 1, tree, searchable),
                                    2 * MAX_NODES,
                                )?;
                            }
                        }
                        "tag" => {
                            let parts = children(value)?;
                            let [tag, child] = parts.as_slice() else {
                                return Err(Error::Invalid(
                                    "RPC highlight tag requires two arguments",
                                ));
                            };
                            match tree {
                                Tree::Message => {
                                    let (kind, code) = constructor(tag)?;
                                    match kind.as_str() {
                                        "expr" => {}
                                        "goal" | "widget" | "trace" => {
                                            return Err(Error::Unsupported(
                                                "RPC highlight of embedded goals, widgets or traces is not implemented",
                                            ));
                                        }
                                        _ => {
                                            return Err(Error::Invalid(
                                                "unknown RPC highlight message embedding",
                                            ));
                                        }
                                    }
                                    push(&mut work, Work::Expression, 2 * MAX_NODES)?;
                                    // findTaggedTextMatches replaces the entire message tag
                                    // with code.stripTags. Its fallback child is omitted from
                                    // discovery, but highlightTaggedText.go still visits that
                                    // child after the code while advancing its byte offset.
                                    push(
                                        &mut work,
                                        Work::Read(child, depth + 1, Tree::Message, false),
                                        2 * MAX_NODES,
                                    )?;
                                    push(
                                        &mut work,
                                        Work::Read(code, depth + 1, Tree::Code, searchable),
                                        2 * MAX_NODES,
                                    )?;
                                }
                                Tree::Code => {
                                    let info = SubexprInfo::decode(tag, format)?;
                                    push(&mut work, Work::Info(info), 2 * MAX_NODES)?;
                                    push(
                                        &mut work,
                                        Work::Read(child, depth + 1, Tree::Code, searchable),
                                        2 * MAX_NODES,
                                    )?;
                                }
                            }
                        }
                        _ => {
                            return Err(Error::Invalid(
                                "unknown RPC highlight message constructor",
                            ));
                        }
                    }
                }
                Work::Append(count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .ok_or(Error::Invalid("RPC highlight message has an invalid tree"))?;
                    let children = values.split_off(start);
                    let index = nodes.len();
                    push(&mut nodes, Node::Append(children), MAX_NODES)?;
                    push(&mut values, index, MAX_NODES)?;
                }
                Work::Expression => {
                    let child = values
                        .pop()
                        .ok_or(Error::Invalid("RPC highlight expression has no child"))?;
                    let code = values
                        .pop()
                        .ok_or(Error::Invalid("RPC highlight expression has no code"))?;
                    let index = nodes.len();
                    push(&mut nodes, Node::Expression { code, child }, MAX_NODES)?;
                    push(&mut values, index, MAX_NODES)?;
                }
                Work::Info(info) => {
                    let child = values
                        .pop()
                        .ok_or(Error::Invalid("RPC highlight expression info has no child"))?;
                    let index = nodes.len();
                    push(&mut nodes, Node::Info { info, child }, MAX_NODES)?;
                    push(&mut values, index, MAX_NODES)?;
                }
            }
        }
        if values.len() != 1 {
            return Err(Error::Invalid("RPC highlight message has no unique root"));
        }
        Ok(Self {
            nodes,
            text,
            search_text,
            root: values[0],
        })
    }
}

// KMP retains overlapping UTF-8 byte matches, as the pinned implementation
// does. Both strings are validated UTF-8; a complete match therefore begins
// and ends at character boundaries even for supplementary-plane characters.
fn match_positions(query: &str, text: &str) -> Result<Vec<usize>> {
    let pattern = query.as_bytes();
    let mut matches = Vec::new();
    if pattern.is_empty() || pattern.len() > text.len() {
        return Ok(matches);
    }
    let mut prefix = Vec::new();
    prefix
        .try_reserve_exact(pattern.len())
        .map_err(|_| Error::Limit("RPC highlight search allocation failed"))?;
    prefix.resize(pattern.len(), 0usize);
    let mut length = 0;
    for index in 1..pattern.len() {
        while length != 0 && pattern[index] != pattern[length] {
            length = prefix[length - 1];
        }
        if pattern[index] == pattern[length] {
            length += 1;
        }
        prefix[index] = length;
    }
    length = 0;
    for (index, byte) in text.bytes().enumerate() {
        while length != 0 && byte != pattern[length] {
            length = prefix[length - 1];
        }
        if byte == pattern[length] {
            length += 1;
        }
        if length == pattern.len() {
            push(&mut matches, index + 1 - length, MAX_MATCHES)?;
            length = prefix[length - 1];
        }
    }
    Ok(matches)
}

struct Writer {
    output: String,
    limit: usize,
}
impl Writer {
    fn push(&mut self, text: &str) -> Result<()> {
        self.output
            .len()
            .checked_add(text.len())
            .filter(|bytes| *bytes <= self.limit)
            .ok_or(Error::Limit(
                "RPC highlight response exceeds its wire budget",
            ))?;
        self.output
            .try_reserve(text.len())
            .map_err(|_| Error::Limit("RPC highlight response allocation failed"))?;
        self.output.push_str(text);
        Ok(())
    }

    // Check escaped output as it is written; never allocate an unbounded
    // intermediate JSON string before discovering that the response is full.
    fn quoted(&mut self, text: &str) -> Result<()> {
        const HEX: &str = "0123456789abcdef";
        self.push("\"")?;
        let mut start = 0;
        for (index, character) in text.char_indices() {
            let escape = match character {
                '"' => "\\\"",
                '\\' => "\\\\",
                '\n' => "\\n",
                '\r' => "\\r",
                '\t' => "\\t",
                '\u{0008}' => "\\b",
                '\u{000c}' => "\\f",
                c if c < ' ' => "",
                _ => continue,
            };
            self.push(&text[start..index])?;
            if escape.is_empty() {
                let byte = character as usize;
                self.push("\\u00")?;
                self.push(&HEX[byte >> 4..(byte >> 4) + 1])?;
                self.push(&HEX[byte & 15..(byte & 15) + 1])?;
            } else {
                self.push(escape)?;
            }
            start = index + character.len_utf8();
        }
        self.push(&text[start..])?;
        self.push("\"")
    }

    fn text(&mut self, text: &str, highlighted: bool) -> Result<()> {
        if highlighted {
            self.push("{\"tag\":[\"highlighted\",")?;
        }
        self.push("{\"text\":")?;
        self.quoted(text)?;
        self.push("}")?;
        if highlighted {
            self.push("]}")?;
        }
        Ok(())
    }

    fn info(&mut self, info: &SubexprInfo, format: WireFormat) -> Result<()> {
        self.push("{\"info\":")?;
        self.push(&format.reference(info.reference))?;
        self.push(",\"subexprPos\":")?;
        self.quoted(&info.position)?;
        if let Some(status) = info.diff_status {
            self.push(",\"diffStatus\":")?;
            self.quoted(status)?;
        }
        self.push("}")
    }
}

// Clip each global match to this leaf. In particular, do not merge overlapping
// matches or skip one merely because a preceding highlight crossed its start:
// the pinned highlighter emits that match too, until this leaf is exhausted.
fn pieces(
    text: &str,
    offset: usize,
    query_bytes: usize,
    matches: &[usize],
    mut emit: impl FnMut(bool, &str) -> Result<()>,
) -> Result<()> {
    let mut cursor = 0;
    let mut any_match = false;
    for &global_start in matches {
        if cursor >= text.len() {
            break;
        }
        let start = global_start.saturating_sub(offset);
        if start >= text.len() {
            break;
        }
        if cursor < start {
            let part = text.get(cursor..start).ok_or(Error::Invalid(
                "RPC highlight match splits a UTF-8 character",
            ))?;
            emit(false, part)?;
        }
        let end = (global_start + query_bytes).saturating_sub(offset);
        let part = text.get(start..end.min(text.len())).ok_or(Error::Invalid(
            "RPC highlight match splits a UTF-8 character",
        ))?;
        emit(true, part)?;
        cursor = end;
        any_match = true;
    }
    if !any_match {
        emit(false, text)?;
    } else if cursor < text.len() {
        let part = text.get(cursor..).ok_or(Error::Invalid(
            "RPC highlight match splits a UTF-8 character",
        ))?;
        emit(false, part)?;
    }
    Ok(())
}

fn render(
    message: &Message,
    query: &str,
    matches: &[usize],
    format: WireFormat,
    limit: usize,
) -> Result<String> {
    enum Work {
        Node(usize),
        Syntax(&'static str),
    }
    let mut writer = Writer {
        output: String::new(),
        limit,
    };
    let mut work = Vec::new();
    let mut first_match = 0;
    push(&mut work, Work::Node(message.root), 2 * MAX_NODES)?;
    while let Some(task) = work.pop() {
        match task {
            Work::Syntax(syntax) => writer.push(syntax)?,
            Work::Node(index) => match &message.nodes[index] {
                Node::Append(children) => {
                    writer.push("{\"append\":[")?;
                    push(&mut work, Work::Syntax("]}"), 2 * MAX_NODES)?;
                    for (position, &child) in children.iter().enumerate().rev() {
                        push(&mut work, Work::Node(child), 2 * MAX_NODES)?;
                        if position != 0 {
                            push(&mut work, Work::Syntax(","), 2 * MAX_NODES)?;
                        }
                    }
                }
                Node::Expression { code, child } => {
                    writer.push("{\"tag\":[{\"expr\":")?;
                    push(&mut work, Work::Syntax("]}"), 2 * MAX_NODES)?;
                    push(&mut work, Work::Node(*child), 2 * MAX_NODES)?;
                    push(&mut work, Work::Syntax("},"), 2 * MAX_NODES)?;
                    push(&mut work, Work::Node(*code), 2 * MAX_NODES)?;
                }
                Node::Info { info, child } => {
                    writer.push("{\"tag\":[")?;
                    writer.info(info, format)?;
                    writer.push(",")?;
                    push(&mut work, Work::Syntax("]}"), 2 * MAX_NODES)?;
                    push(&mut work, Work::Node(*child), 2 * MAX_NODES)?;
                }
                Node::Text(span) => {
                    let text = &message.text[span.clone()];
                    let active = &matches[first_match..];
                    let mut count = 0;
                    pieces(text, span.start, query.len(), active, |_, _| {
                        count += 1;
                        Ok(())
                    })?;
                    if count > 1 {
                        writer.push("{\"append\":[")?;
                    }
                    let mut first = true;
                    pieces(
                        text,
                        span.start,
                        query.len(),
                        active,
                        |highlighted, part| {
                            if !first {
                                writer.push(",")?;
                            }
                            first = false;
                            writer.text(part, highlighted)
                        },
                    )?;
                    if count > 1 {
                        writer.push("]}")?;
                    }
                    while first_match < matches.len()
                        && matches[first_match] + query.len() <= span.end
                    {
                        first_match += 1;
                    }
                }
            },
        }
    }
    Ok(writer.output)
}

pub(in crate::dispatch) struct Request {
    query: String,
    message: Message,
    format: WireFormat,
}

impl Request {
    pub(in crate::dispatch) fn decode(value: RawField<'_>, format: WireFormat) -> Result<Self> {
        let RawField::Value(raw) = value else {
            return Err(Error::Invalid("RPC highlight requires one params object"));
        };
        if raw.len() > MAX_INPUT_BYTES {
            return Err(Error::Limit("RPC highlight request exceeds its byte limit"));
        }
        let raw = object(value).map_err(Error::Invalid)?;
        let DecodedField::Valid(query) = decoded_string_field(value, "query") else {
            return Err(Error::Invalid("RPC highlight requires one query string"));
        };
        if query.len() > MAX_QUERY_BYTES {
            return Err(Error::Limit("RPC highlight query exceeds its byte limit"));
        }
        let RawField::Value(message) = object_field(raw, "msg") else {
            return Err(Error::Invalid("RPC highlight requires one message"));
        };
        Ok(Self {
            query,
            message: Message::decode(message, format)?,
            format,
        })
    }

    // Every occurrence will be encoded once in the response, including nested
    // and repeated tags. The session must retain each one, even for no matches.
    pub(in crate::dispatch) fn references(&self) -> impl Iterator<Item = u64> + '_ {
        self.message.nodes.iter().filter_map(|node| match node {
            Node::Info { info, .. } => Some(info.reference),
            _ => None,
        })
    }

    pub(in crate::dispatch) fn response(&self, limit: usize) -> Result<String> {
        let matches = match_positions(&self.query, &self.message.search_text)?;
        render(&self.message, &self.query, &matches, self.format, limit)
    }
}

#[cfg(test)]
mod tests;
