#![forbid(unsafe_code)]

//! Read-only validator for `fln.agent-frontier/1` capsules embedded in live
//! bead comments.
//!
//! The guard deliberately has no write path. It reads `.beads/issues.jsonl`,
//! parses the JSONL and any fenced capsule objects, and reports malformed or
//! stale control state. Missing capsules are warnings during the migration
//! period and become errors under `--strict`.

use std::collections::BTreeMap;
use std::env;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::{Path, PathBuf};

const SCHEMA: &str = "fln.agent-frontier/1";
const DEFAULT_PATH: &str = ".beads/issues.jsonl";

#[derive(Debug, Clone, PartialEq)]
enum Json {
    Null,
    Bool,
    Number,
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

impl Json {
    fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    fn as_array(&self) -> Option<&[Json]> {
        match self {
            Self::Array(values) => Some(values),
            _ => None,
        }
    }

    fn as_object(&self) -> Option<&BTreeMap<String, Json>> {
        match self {
            Self::Object(fields) => Some(fields),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParseError {
    offset: usize,
    message: &'static str,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "byte {}: {}", self.offset, self.message)
    }
}

struct Parser<'a> {
    input: &'a [u8],
    cursor: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            cursor: 0,
        }
    }

    fn parse(mut self) -> Result<Json, ParseError> {
        self.skip_ws();
        let value = self.value()?;
        self.skip_ws();
        if self.cursor != self.input.len() {
            return Err(self.error("trailing bytes after JSON value"));
        }
        Ok(value)
    }

    fn value(&mut self) -> Result<Json, ParseError> {
        self.skip_ws();
        match self.peek() {
            Some(b'n') => self.literal(b"null", Json::Null),
            Some(b't') => self.literal(b"true", Json::Bool),
            Some(b'f') => self.literal(b"false", Json::Bool),
            Some(b'"') => self.string().map(Json::String),
            Some(b'[') => self.array(),
            Some(b'{') => self.object(),
            Some(b'-') | Some(b'0'..=b'9') => {
                self.number()?;
                Ok(Json::Number)
            }
            Some(_) => Err(self.error("unexpected token")),
            None => Err(self.error("unexpected end of input")),
        }
    }

    fn literal(&mut self, expected: &[u8], value: Json) -> Result<Json, ParseError> {
        if self
            .input
            .get(self.cursor..self.cursor.saturating_add(expected.len()))
            == Some(expected)
        {
            self.cursor += expected.len();
            Ok(value)
        } else {
            Err(self.error("invalid literal"))
        }
    }

    fn object(&mut self) -> Result<Json, ParseError> {
        self.expect(b'{')?;
        self.skip_ws();
        let mut fields = BTreeMap::new();
        if self.take(b'}') {
            return Ok(Json::Object(fields));
        }
        loop {
            self.skip_ws();
            if self.peek() != Some(b'"') {
                return Err(self.error("object key must be a string"));
            }
            let key = self.string()?;
            self.skip_ws();
            self.expect(b':')?;
            let value = self.value()?;
            if fields.insert(key, value).is_some() {
                return Err(self.error("duplicate object key"));
            }
            self.skip_ws();
            if self.take(b'}') {
                break;
            }
            self.expect(b',')?;
        }
        Ok(Json::Object(fields))
    }

    fn array(&mut self) -> Result<Json, ParseError> {
        self.expect(b'[')?;
        self.skip_ws();
        let mut values = Vec::new();
        if self.take(b']') {
            return Ok(Json::Array(values));
        }
        loop {
            values.push(self.value()?);
            self.skip_ws();
            if self.take(b']') {
                break;
            }
            self.expect(b',')?;
        }
        Ok(Json::Array(values))
    }

    fn string(&mut self) -> Result<String, ParseError> {
        self.expect(b'"')?;
        let mut output = String::new();
        loop {
            let byte = self
                .next()
                .ok_or_else(|| self.error("unterminated string"))?;
            match byte {
                b'"' => return Ok(output),
                b'\\' => self.escape(&mut output)?,
                0x00..=0x1f => return Err(self.error("control byte in string")),
                0x20..=0x7f => output.push(char::from(byte)),
                _ => {
                    let start = self.cursor - 1;
                    let width = utf8_width(byte)
                        .ok_or_else(|| self.error_at(start, "invalid UTF-8 leading byte"))?;
                    let end = start.saturating_add(width);
                    let bytes = self
                        .input
                        .get(start..end)
                        .ok_or_else(|| self.error_at(start, "truncated UTF-8 sequence"))?;
                    let text = std::str::from_utf8(bytes)
                        .map_err(|_| self.error_at(start, "invalid UTF-8 sequence"))?;
                    output.push_str(text);
                    self.cursor = end;
                }
            }
        }
    }

    fn escape(&mut self, output: &mut String) -> Result<(), ParseError> {
        let escaped = self
            .next()
            .ok_or_else(|| self.error("truncated string escape"))?;
        match escaped {
            b'"' => output.push('"'),
            b'\\' => output.push('\\'),
            b'/' => output.push('/'),
            b'b' => output.push('\u{0008}'),
            b'f' => output.push('\u{000c}'),
            b'n' => output.push('\n'),
            b'r' => output.push('\r'),
            b't' => output.push('\t'),
            b'u' => {
                let first = self.hex_quad()?;
                let scalar = if (0xd800..=0xdbff).contains(&first) {
                    if self.next() != Some(b'\\') || self.next() != Some(b'u') {
                        return Err(self.error("high surrogate without low surrogate"));
                    }
                    let second = self.hex_quad()?;
                    if !(0xdc00..=0xdfff).contains(&second) {
                        return Err(self.error("high surrogate followed by non-low surrogate"));
                    }
                    0x1_0000 + ((u32::from(first) - 0xd800) << 10) + (u32::from(second) - 0xdc00)
                } else if (0xdc00..=0xdfff).contains(&first) {
                    return Err(self.error("unpaired low surrogate"));
                } else {
                    u32::from(first)
                };
                output.push(
                    char::from_u32(scalar)
                        .ok_or_else(|| self.error("invalid Unicode scalar value"))?,
                );
            }
            _ => return Err(self.error("unknown string escape")),
        }
        Ok(())
    }

    fn hex_quad(&mut self) -> Result<u16, ParseError> {
        let start = self.cursor;
        let bytes = self
            .input
            .get(start..start.saturating_add(4))
            .ok_or_else(|| self.error_at(start, "truncated Unicode escape"))?;
        let mut value = 0u16;
        for byte in bytes {
            value = value
                .checked_mul(16)
                .and_then(|current| hex_value(*byte).map(|digit| current + u16::from(digit)))
                .ok_or_else(|| self.error_at(start, "invalid Unicode escape"))?;
        }
        self.cursor += 4;
        Ok(value)
    }

    fn number(&mut self) -> Result<(), ParseError> {
        let start = self.cursor;
        self.take(b'-');
        match self.peek() {
            Some(b'0') => {
                self.cursor += 1;
                if matches!(self.peek(), Some(b'0'..=b'9')) {
                    return Err(self.error("leading zero in number"));
                }
            }
            Some(b'1'..=b'9') => {
                self.cursor += 1;
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.cursor += 1;
                }
            }
            _ => return Err(self.error("invalid number")),
        }
        if self.take(b'.') {
            let fraction = self.cursor;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.cursor += 1;
            }
            if self.cursor == fraction {
                return Err(self.error("fraction has no digits"));
            }
        }
        if matches!(self.peek(), Some(b'e') | Some(b'E')) {
            self.cursor += 1;
            if matches!(self.peek(), Some(b'+') | Some(b'-')) {
                self.cursor += 1;
            }
            let exponent = self.cursor;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.cursor += 1;
            }
            if self.cursor == exponent {
                return Err(self.error("exponent has no digits"));
            }
        }
        std::str::from_utf8(&self.input[start..self.cursor])
            .map_err(|_| self.error_at(start, "invalid number encoding"))?;
        Ok(())
    }

    fn skip_ws(&mut self) {
        while matches!(
            self.peek(),
            Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
        ) {
            self.cursor += 1;
        }
    }

    fn expect(&mut self, wanted: u8) -> Result<(), ParseError> {
        if self.take(wanted) {
            Ok(())
        } else {
            Err(self.error("unexpected delimiter"))
        }
    }

    fn take(&mut self, wanted: u8) -> bool {
        if self.peek() == Some(wanted) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    fn next(&mut self) -> Option<u8> {
        let byte = self.peek()?;
        self.cursor += 1;
        Some(byte)
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.cursor).copied()
    }

    fn error(&self, message: &'static str) -> ParseError {
        self.error_at(self.cursor, message)
    }

    fn error_at(&self, offset: usize, message: &'static str) -> ParseError {
        ParseError { offset, message }
    }
}

fn utf8_width(first: u8) -> Option<usize> {
    match first {
        0xc2..=0xdf => Some(2),
        0xe0..=0xef => Some(3),
        0xf0..=0xf4 => Some(4),
        _ => None,
    }
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Severity {
    Warning,
    Error,
}

impl Severity {
    const fn label(self) -> &'static str {
        match self {
            Self::Warning => "warning",
            Self::Error => "error",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Finding {
    severity: Severity,
    line: usize,
    bead: Option<String>,
    code: &'static str,
    message: String,
}

#[derive(Debug, Default)]
struct Report {
    issues: usize,
    active: usize,
    capsules: usize,
    findings: Vec<Finding>,
}

impl Report {
    fn error_count(&self) -> usize {
        self.findings
            .iter()
            .filter(|finding| finding.severity == Severity::Error)
            .count()
    }

    fn warning_count(&self) -> usize {
        self.findings
            .iter()
            .filter(|finding| finding.severity == Severity::Warning)
            .count()
    }
}

fn field<'a>(object: &'a BTreeMap<String, Json>, key: &str) -> Option<&'a Json> {
    object.get(key)
}

fn string_field<'a>(object: &'a BTreeMap<String, Json>, key: &str) -> Option<&'a str> {
    field(object, key).and_then(Json::as_str)
}

fn require_nonempty_string(
    object: &BTreeMap<String, Json>,
    key: &str,
    path: &str,
    problems: &mut Vec<String>,
) {
    if !matches!(string_field(object, key), Some(value) if !value.trim().is_empty()) {
        problems.push(format!("{path}.{key} must be a non-empty string"));
    }
}

fn object_field<'a>(
    object: &'a BTreeMap<String, Json>,
    key: &str,
    path: &str,
    problems: &mut Vec<String>,
) -> Option<&'a BTreeMap<String, Json>> {
    match field(object, key).and_then(Json::as_object) {
        Some(value) => Some(value),
        None => {
            problems.push(format!("{path}.{key} must be an object"));
            None
        }
    }
}

fn array_field<'a>(
    object: &'a BTreeMap<String, Json>,
    key: &str,
    path: &str,
    problems: &mut Vec<String>,
) -> Option<&'a [Json]> {
    match field(object, key).and_then(Json::as_array) {
        Some(value) => Some(value),
        None => {
            problems.push(format!("{path}.{key} must be an array"));
            None
        }
    }
}

fn nonempty_string_array(
    object: &BTreeMap<String, Json>,
    key: &str,
    path: &str,
    problems: &mut Vec<String>,
) {
    let Some(values) = array_field(object, key, path, problems) else {
        return;
    };
    if values.is_empty() {
        problems.push(format!("{path}.{key} must not be empty"));
        return;
    }
    for (index, value) in values.iter().enumerate() {
        if !matches!(value.as_str(), Some(text) if !text.trim().is_empty()) {
            problems.push(format!("{path}.{key}[{index}] must be a non-empty string"));
        }
    }
}

fn is_hex(value: &str, length: usize) -> bool {
    value.len() == length && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn is_sha256(value: &str) -> bool {
    value
        .strip_prefix("sha256:")
        .is_some_and(|digest| is_hex(digest, 64))
}

fn validate_capsule(capsule: &Json, issue_id: &str, issue_status: &str) -> Result<(), Vec<String>> {
    let mut problems = Vec::new();
    let Some(root) = capsule.as_object() else {
        return Err(vec!["capsule root must be an object".to_owned()]);
    };

    if string_field(root, "schema") != Some(SCHEMA) {
        problems.push(format!("schema must be {SCHEMA:?}"));
    }
    if string_field(root, "bead") != Some(issue_id) {
        problems.push(format!("bead must match issue id {issue_id:?}"));
    }
    require_nonempty_string(root, "state", "capsule", &mut problems);
    let state = string_field(root, "state").filter(|value| !value.trim().is_empty());
    if state != Some(issue_status) {
        problems.push(format!(
            "capsule.state must match issue status {issue_status:?}"
        ));
    }
    require_nonempty_string(root, "owner", "capsule", &mut problems);
    require_nonempty_string(root, "lease_observed_at", "capsule", &mut problems);

    if let Some(anchor) = object_field(root, "anchor", "capsule", &mut problems) {
        require_nonempty_string(anchor, "branch", "capsule.anchor", &mut problems);
        for key in ["commit", "tree"] {
            match string_field(anchor, key) {
                Some(value) if is_hex(value, 40) => {}
                _ => problems.push(format!(
                    "capsule.anchor.{key} must be a 40-hex Git object id"
                )),
            }
        }
        match field(anchor, "tracked_blobs").and_then(Json::as_object) {
            Some(blobs) if !blobs.is_empty() => {
                for (path, digest) in blobs {
                    if path.trim().is_empty()
                        || !matches!(digest.as_str(), Some(value) if is_hex(value, 40))
                    {
                        problems.push(
                            "capsule.anchor.tracked_blobs must map non-empty paths to 40-hex blob ids"
                                .to_owned(),
                        );
                        break;
                    }
                }
            }
            _ => {
                problems.push("capsule.anchor.tracked_blobs must be a non-empty object".to_owned())
            }
        }
    }

    if let Some(frontier) = object_field(root, "frontier", "capsule", &mut problems) {
        for key in [
            "artifact",
            "pipeline",
            "last_proven",
            "first_failure",
            "failure_class",
        ] {
            require_nonempty_string(frontier, key, "capsule.frontier", &mut problems);
        }
        for key in ["actual_fingerprint", "expected_fingerprint"] {
            match string_field(frontier, key) {
                Some(value) if is_sha256(value) => {}
                _ => problems.push(format!("capsule.frontier.{key} must be sha256:<64 hex>")),
            }
        }
    }

    if let Some(hypothesis) = object_field(root, "hypothesis", "capsule", &mut problems) {
        require_nonempty_string(hypothesis, "statement", "capsule.hypothesis", &mut problems);
        require_nonempty_string(
            hypothesis,
            "smallest_experiment",
            "capsule.hypothesis",
            &mut problems,
        );
        nonempty_string_array(
            hypothesis,
            "protected_surfaces",
            "capsule.hypothesis",
            &mut problems,
        );
    }

    if let Some(last_green) = object_field(root, "last_green", "capsule", &mut problems) {
        match string_field(last_green, "commit") {
            Some(value) if is_hex(value, 40) => {}
            _ => problems.push("capsule.last_green.commit must be a 40-hex commit id".to_owned()),
        }
        nonempty_string_array(last_green, "commands", "capsule.last_green", &mut problems);
        if let Some(receipts) =
            array_field(last_green, "receipts", "capsule.last_green", &mut problems)
        {
            for (index, receipt) in receipts.iter().enumerate() {
                if !matches!(receipt.as_str(), Some(value) if !value.trim().is_empty()) {
                    problems.push(format!(
                        "capsule.last_green.receipts[{index}] must be a non-empty string"
                    ));
                }
            }
        }
        require_nonempty_string(last_green, "scope", "capsule.last_green", &mut problems);
    }

    if let Some(rows) = array_field(root, "negative_evidence", "capsule", &mut problems) {
        for (index, row) in rows.iter().enumerate() {
            let Some(row) = row.as_object() else {
                problems.push(format!(
                    "capsule.negative_evidence[{index}] must be an object"
                ));
                continue;
            };
            let path = format!("capsule.negative_evidence[{index}]");
            for key in [
                "attempt",
                "hypothesis",
                "outcome",
                "reason",
                "differentiator_required",
            ] {
                require_nonempty_string(row, key, &path, &mut problems);
            }
        }
    }

    if let Some(next) = object_field(root, "next", "capsule", &mut problems) {
        for key in ["command", "success", "failure_capture"] {
            require_nonempty_string(next, key, "capsule.next", &mut problems);
        }
    }

    if let Some(closure) = object_field(root, "closure", "capsule", &mut problems) {
        nonempty_string_array(closure, "criteria", "capsule.closure", &mut problems);
        if let Some(missing) =
            array_field(closure, "still_missing", "capsule.closure", &mut problems)
        {
            for (index, item) in missing.iter().enumerate() {
                if !matches!(item.as_str(), Some(value) if !value.trim().is_empty()) {
                    problems.push(format!(
                        "capsule.closure.still_missing[{index}] must be a non-empty string"
                    ));
                }
            }
            if issue_status == "closed" && !missing.is_empty() {
                problems.push(
                    "closed bead cannot retain capsule.closure.still_missing entries".to_owned(),
                );
            }
        }
    }

    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems)
    }
}

fn fenced_json_blocks(text: &str) -> Vec<&str> {
    let mut blocks = Vec::new();
    let mut cursor = 0usize;
    while let Some(relative) = text[cursor..].find("```") {
        let fence = cursor + relative;
        let language_start = fence + 3;
        let Some(line_end_relative) = text[language_start..].find('\n') else {
            break;
        };
        let line_end = language_start + line_end_relative;
        let language = text[language_start..line_end].trim();
        let body_start = line_end + 1;
        let Some(close_relative) = text[body_start..].find("```") else {
            break;
        };
        let body_end = body_start + close_relative;
        if language.is_empty() || language.eq_ignore_ascii_case("json") {
            blocks.push(text[body_start..body_end].trim());
        }
        cursor = body_end + 3;
    }
    blocks
}

fn latest_capsule(comments: &[Json]) -> Result<Option<Json>, String> {
    let mut latest = None;
    for comment in comments {
        let Some(comment) = comment.as_object() else {
            continue;
        };
        let Some(text) = string_field(comment, "text") else {
            continue;
        };
        for block in fenced_json_blocks(text) {
            if !block.contains(SCHEMA) {
                continue;
            }
            let parsed = Parser::new(block)
                .parse()
                .map_err(|error| format!("frontier capsule JSON is malformed: {error}"))?;
            if parsed
                .as_object()
                .and_then(|object| string_field(object, "schema"))
                == Some(SCHEMA)
            {
                latest = Some(parsed);
            }
        }
    }
    Ok(latest)
}

fn inspect_issue(line: usize, issue: Json, strict: bool, report: &mut Report) {
    report.issues += 1;
    let Some(object) = issue.as_object() else {
        report.findings.push(Finding {
            severity: Severity::Error,
            line,
            bead: None,
            code: "FLN-FRONTIER-ISSUE-SHAPE",
            message: "issue row must be a JSON object".to_owned(),
        });
        return;
    };
    let id = string_field(object, "id").unwrap_or("<missing-id>");
    let status = string_field(object, "status").unwrap_or("<missing-status>");
    let active = status == "in_progress";
    if active {
        report.active += 1;
    }
    let comments = field(object, "comments")
        .and_then(Json::as_array)
        .unwrap_or(&[]);
    let capsule = match latest_capsule(comments) {
        Ok(capsule) => capsule,
        Err(message) => {
            report.findings.push(Finding {
                severity: Severity::Error,
                line,
                bead: Some(id.to_owned()),
                code: "FLN-FRONTIER-CAPSULE-PARSE",
                message,
            });
            return;
        }
    };
    let Some(capsule) = capsule else {
        if active {
            report.findings.push(Finding {
                severity: if strict {
                    Severity::Error
                } else {
                    Severity::Warning
                },
                line,
                bead: Some(id.to_owned()),
                code: "FLN-FRONTIER-MISSING",
                message: "in-progress bead has no fln.agent-frontier/1 capsule".to_owned(),
            });
        }
        return;
    };
    report.capsules += 1;
    if let Err(problems) = validate_capsule(&capsule, id, status) {
        for message in problems {
            report.findings.push(Finding {
                severity: Severity::Error,
                line,
                bead: Some(id.to_owned()),
                code: "FLN-FRONTIER-CAPSULE-INVALID",
                message,
            });
        }
    }
}

fn inspect(path: &Path, strict: bool) -> io::Result<Report> {
    let file = File::open(path)?;
    let mut report = Report::default();
    for (index, line) in BufReader::new(file).lines().enumerate() {
        let line_number = index + 1;
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        match Parser::new(&line).parse() {
            Ok(issue) => inspect_issue(line_number, issue, strict, &mut report),
            Err(error) => report.findings.push(Finding {
                severity: Severity::Error,
                line: line_number,
                bead: None,
                code: "FLN-FRONTIER-JSONL-PARSE",
                message: error.to_string(),
            }),
        }
    }
    Ok(report)
}

#[derive(Debug)]
struct Options {
    path: PathBuf,
    strict: bool,
    json: bool,
}

fn usage() -> &'static str {
    "usage: fln-frontier-guard [--strict] [--json] [PATH]\n\
     \n\
     PATH defaults to .beads/issues.jsonl. Missing capsules are warnings unless\n\
     --strict is supplied; malformed present capsules always fail."
}

fn options() -> Result<Options, String> {
    let mut path = None;
    let mut strict = false;
    let mut json = false;
    for argument in env::args().skip(1) {
        match argument.as_str() {
            "--strict" => strict = true,
            "--json" => json = true,
            "-h" | "--help" => return Err(usage().to_owned()),
            value if value.starts_with('-') => {
                return Err(format!("unknown option {value:?}\n{}", usage()));
            }
            value if path.is_none() => path = Some(PathBuf::from(value)),
            value => return Err(format!("unexpected argument {value:?}\n{}", usage())),
        }
    }
    Ok(Options {
        path: path.unwrap_or_else(|| PathBuf::from(DEFAULT_PATH)),
        strict,
        json,
    })
}

fn json_escape(value: &str) -> String {
    let mut output = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{001f}' => {
                use std::fmt::Write as _;
                let _ = write!(output, "\\u{:04x}", u32::from(character));
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

fn render_json(report: &Report) {
    println!(
        "{{\"schema\":\"fln.frontier-guard/1\",\"issues\":{},\"active\":{},\"capsules\":{},\"errors\":{},\"warnings\":{},\"findings\":[",
        report.issues,
        report.active,
        report.capsules,
        report.error_count(),
        report.warning_count()
    );
    for (index, finding) in report.findings.iter().enumerate() {
        if index != 0 {
            println!(",");
        }
        let bead = finding
            .bead
            .as_deref()
            .map(json_escape)
            .unwrap_or_else(|| "null".to_owned());
        print!(
            "{{\"severity\":{},\"line\":{},\"bead\":{},\"code\":{},\"message\":{}}}",
            json_escape(finding.severity.label()),
            finding.line,
            bead,
            json_escape(finding.code),
            json_escape(&finding.message)
        );
    }
    println!("]}}");
}

fn render_human(path: &Path, report: &Report) {
    for finding in &report.findings {
        let bead = finding
            .bead
            .as_deref()
            .map(|value| format!(" {value}"))
            .unwrap_or_default();
        eprintln!(
            "{}:{}:{}{}: {}: {}",
            path.display(),
            finding.line,
            finding.severity.label(),
            bead,
            finding.code,
            finding.message
        );
    }
    eprintln!(
        "frontier-guard: {} issue rows, {} active, {} capsules, {} errors, {} warnings",
        report.issues,
        report.active,
        report.capsules,
        report.error_count(),
        report.warning_count()
    );
}

fn main() {
    let options = match options() {
        Ok(options) => options,
        Err(message) if message == usage() => {
            println!("{message}");
            return;
        }
        Err(message) => {
            eprintln!("{message}");
            std::process::exit(2);
        }
    };
    let report = match inspect(&options.path, options.strict) {
        Ok(report) => report,
        Err(error) => {
            eprintln!(
                "frontier-guard: cannot read {}: {error}",
                options.path.display()
            );
            std::process::exit(2);
        }
    };
    if options.json {
        render_json(&report);
    } else {
        render_human(&options.path, &report);
    }
    if report.error_count() != 0 {
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";
    const TREE: &str = "89abcdef0123456789abcdef0123456789abcdef";
    const DIGEST: &str = "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

    fn capsule(bead: &str, state: &str, missing: &str) -> String {
        format!(
            r#"{{
  "schema":"fln.agent-frontier/1",
  "bead":"{bead}",
  "state":"{state}",
  "owner":"test-agent",
  "lease_observed_at":"2026-08-31T20:15:37Z",
  "anchor":{{
    "branch":"main",
    "commit":"{COMMIT}",
    "tree":"{TREE}",
    "tracked_blobs":{{"src/lib.rs":"{COMMIT}"}}
  }},
  "frontier":{{
    "artifact":"fixture",
    "pipeline":"decode -> check",
    "last_proven":"item 1",
    "first_failure":"item 2",
    "failure_class":"shape",
    "actual_fingerprint":"{DIGEST}",
    "expected_fingerprint":"{DIGEST}"
  }},
  "hypothesis":{{
    "statement":"one field is wrong",
    "smallest_experiment":"change that field",
    "protected_surfaces":["everything else"]
  }},
  "last_green":{{
    "commit":"{COMMIT}",
    "commands":["cargo test"],
    "receipts":[],
    "scope":"synthetic"
  }},
  "negative_evidence":[],
  "next":{{
    "command":"cargo test",
    "success":"frontier advances",
    "failure_capture":"first divergent path"
  }},
  "closure":{{
    "criteria":["real artifact passes"],
    "still_missing":[{missing}]
  }}
}}"#
        )
    }

    fn issue(bead: &str, status: &str, capsule: Option<&str>) -> Json {
        let comment = capsule
            .map(|capsule| {
                format!(
                    "{{\"text\":{}}}",
                    json_escape(&format!("frontier\n```json\n{capsule}\n```"))
                )
            })
            .unwrap_or_else(|| "{\"text\":\"ordinary comment\"}".to_owned());
        Parser::new(&format!(
            "{{\"id\":\"{bead}\",\"status\":\"{status}\",\"comments\":[{comment}]}}"
        ))
        .parse()
        .expect("test issue parses")
    }

    #[test]
    fn parser_decodes_utf16_surrogate_pairs() {
        let parsed = Parser::new(r#""\ud83e\udd16""#)
            .parse()
            .expect("robot scalar parses");
        assert_eq!(parsed, Json::String("🤖".to_owned()));
    }

    #[test]
    fn parser_refuses_an_unpaired_surrogate() {
        let error = Parser::new(r#""\ud83eX""#)
            .parse()
            .expect_err("unpaired surrogate must fail");
        assert!(error.message.contains("surrogate"));
    }

    #[test]
    fn latest_capsule_ignores_non_frontier_json_blocks() {
        let valid = capsule("fln-demo", "in_progress", "\"real run\"");
        let comments = vec![Json::Object(BTreeMap::from([(
            "text".to_owned(),
            Json::String(format!(
                "```json\n{{\"kind\":\"other\"}}\n```\n```json\n{valid}\n```"
            )),
        )]))];
        let found = latest_capsule(&comments)
            .expect("capsule search succeeds")
            .expect("frontier capsule found");
        assert_eq!(
            found
                .as_object()
                .and_then(|object| string_field(object, "bead")),
            Some("fln-demo")
        );
    }

    #[test]
    fn valid_in_progress_capsule_passes() {
        let valid = capsule("fln-demo", "in_progress", "\"real run\"");
        let issue = issue("fln-demo", "in_progress", Some(&valid));
        let mut report = Report::default();
        inspect_issue(1, issue, true, &mut report);
        assert_eq!(report.capsules, 1);
        assert_eq!(report.error_count(), 0, "{:?}", report.findings);
    }

    #[test]
    fn migration_mode_warns_but_strict_mode_refuses_missing_capsules() {
        let missing = issue("fln-demo", "in_progress", None);
        let mut migration = Report::default();
        inspect_issue(1, missing.clone(), false, &mut migration);
        assert_eq!(migration.error_count(), 0);
        assert_eq!(migration.warning_count(), 1);

        let mut strict = Report::default();
        inspect_issue(1, missing, true, &mut strict);
        assert_eq!(strict.error_count(), 1);
        assert_eq!(strict.findings[0].code, "FLN-FRONTIER-MISSING");
    }

    #[test]
    fn closed_capsule_may_not_claim_missing_close_evidence() {
        let invalid = capsule("fln-demo", "closed", "\"real run\"");
        let issue = issue("fln-demo", "closed", Some(&invalid));
        let mut report = Report::default();
        inspect_issue(1, issue, false, &mut report);
        assert!(report.findings.iter().any(|finding| {
            finding
                .message
                .contains("closed bead cannot retain capsule.closure.still_missing")
        }));
    }

    #[test]
    fn closed_capsule_with_complete_evidence_passes() {
        let valid = capsule("fln-demo", "closed", "");
        let issue = issue("fln-demo", "closed", Some(&valid));
        let mut report = Report::default();
        inspect_issue(1, issue, false, &mut report);
        assert_eq!(report.error_count(), 0, "{:?}", report.findings);
    }
}
