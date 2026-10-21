//! Literal search over the reference-free diagnostic presentations emitted by
//! this server. Contract: Lean/Server/FileWorker/WidgetRequests.lean,
//! `highlightTaggedText` and `highlightStringMatches?` at the locked Reference.
//!
//! Keep the original append tree: matches can cross text nodes, and the pin's
//! treatment of overlapping matches is node-sensitive. Flattening the result
//! or replacing KMP by non-overlapping `str::match_indices` changes that wire
//! behavior. Embedded expressions, goals, widgets and traces need real RPC
//! objects; this implementation refuses them rather than inventing references.
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

// A flat arena avoids recursive traversal and recursive destruction of a
// client-supplied append tree. Text spans refer to one bounded UTF-8 buffer.
enum Node {
    Text(Range<usize>),
    Append(Vec<usize>),
}
struct Message {
    nodes: Vec<Node>,
    text: String,
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
        return Err(Error::Invalid("RPC highlight append requires an array"));
    }
    let mut cursor = skip_ws(bytes, 1);
    let mut result = Vec::new();
    if bytes.get(cursor) == Some(&b']') && skip_ws(bytes, cursor + 1) == bytes.len() {
        return Ok(result);
    }
    loop {
        let end = parse_value_end(raw, cursor, 0).ok_or(Error::Invalid(
            "RPC highlight append contains a malformed child",
        ))?;
        push(&mut result, &raw[cursor..end], MAX_NODES)?;
        cursor = skip_ws(bytes, end);
        match bytes.get(cursor) {
            Some(b']') if skip_ws(bytes, cursor + 1) == bytes.len() => return Ok(result),
            Some(b',') => cursor = skip_ws(bytes, cursor + 1),
            _ => return Err(Error::Invalid("RPC highlight append is malformed")),
        }
    }
}

impl Message {
    fn decode(raw: &str) -> Result<Self> {
        enum Work<'a> {
            Read(&'a str, usize),
            Append(usize),
        }
        let mut nodes = Vec::new();
        let mut text = String::new();
        let mut work = Vec::new();
        let mut values = Vec::new();
        let mut visits = 0usize;
        let mut scanned = 0usize;
        push(&mut work, Work::Read(raw, 0), 2 * MAX_NODES)?;
        while let Some(task) = work.pop() {
            match task {
                Work::Read(raw, depth) => {
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
                            let index = nodes.len();
                            push(&mut nodes, Node::Text(start..end), MAX_NODES)?;
                            push(&mut values, index, MAX_NODES)?;
                        }
                        "append" => {
                            let children = children(value)?;
                            push(&mut work, Work::Append(children.len()), 2 * MAX_NODES)?;
                            for child in children.into_iter().rev() {
                                push(&mut work, Work::Read(child, depth + 1), 2 * MAX_NODES)?;
                            }
                        }
                        "tag" => {
                            return Err(Error::Unsupported(
                                "RPC highlight of embedded expressions, goals, widgets or traces is not implemented",
                            ));
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
            }
        }
        if values.len() != 1 {
            return Err(Error::Invalid("RPC highlight message has no unique root"));
        }
        Ok(Self {
            nodes,
            text,
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
            emit(false, &text[cursor..start])?;
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
        emit(false, &text[cursor..])?;
    }
    Ok(())
}

fn render(message: &Message, query: &str, matches: &[usize], limit: usize) -> Result<String> {
    enum Work {
        Node(usize),
        Comma,
        EndAppend,
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
            Work::Comma => writer.push(",")?,
            Work::EndAppend => writer.push("]}")?,
            Work::Node(index) => match &message.nodes[index] {
                Node::Append(children) => {
                    writer.push("{\"append\":[")?;
                    push(&mut work, Work::EndAppend, 2 * MAX_NODES)?;
                    for (position, &child) in children.iter().enumerate().rev() {
                        push(&mut work, Work::Node(child), 2 * MAX_NODES)?;
                        if position != 0 {
                            push(&mut work, Work::Comma, 2 * MAX_NODES)?;
                        }
                    }
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

pub(in crate::dispatch) fn response(value: RawField<'_>, limit: usize) -> Result<String> {
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
    let message = Message::decode(message)?;
    let matches = match_positions(&query, &message.text)?;
    render(&message, &query, &matches, limit)
}

#[cfg(test)]
mod tests;
