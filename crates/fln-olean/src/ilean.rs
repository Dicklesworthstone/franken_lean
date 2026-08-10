//! Exact pinned-epoch `.ilean` JSON codec (plan §7.3b).
//!
//! The Reference deliberately keeps `.ilean` as compact JSON. This module
//! mirrors the generated epoch/field contract and the compact custom JSON
//! shapes in `Lean.Data.Lsp.Internal`: import tuples, declaration ranges,
//! reference identifiers encoded as JSON object keys, and compact reference
//! locations. Parsing is budgeted and fails typed on malformed or unknown
//! input. Encoding emits the Reference's deterministic compact form.

use std::collections::BTreeMap;

use crate::format;

type IResult<T> = Result<T, IleanError>;

/// Total limits applied before an `.ilean` value becomes authoritative.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IleanBudget {
    /// Maximum input or output bytes.
    pub max_bytes: usize,
    /// Maximum JSON values visited while decoding.
    pub max_values: usize,
    /// Maximum JSON container nesting.
    pub max_depth: usize,
}

impl Default for IleanBudget {
    fn default() -> Self {
        Self {
            max_bytes: 64 * 1024 * 1024,
            max_values: 10_000_000,
            max_depth: 64,
        }
    }
}

/// Typed `.ilean` refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IleanError {
    Budget {
        resource: &'static str,
        limit: usize,
    },
    Syntax {
        offset: usize,
        reason: &'static str,
    },
    Shape {
        context: &'static str,
        reason: &'static str,
    },
    UnknownVersion {
        found: u64,
        expected: u64,
    },
}

impl std::fmt::Display for IleanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Budget { resource, limit } => {
                write!(f, ".ilean {resource} budget exceeded (limit {limit})")
            }
            Self::Syntax { offset, reason } => {
                write!(f, ".ilean JSON syntax at byte {offset}: {reason}")
            }
            Self::Shape { context, reason } => {
                write!(f, ".ilean {context}: {reason}")
            }
            Self::UnknownVersion { found, expected } => {
                write!(f, "unsupported .ilean version {found}, expected {expected}")
            }
        }
    }
}

impl std::error::Error for IleanError {}

/// One compact direct-import row:
/// `[module, isPrivate, isAll, isMeta]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IleanImport {
    pub module: String,
    pub is_private: bool,
    pub is_all: bool,
    pub is_meta: bool,
}

/// The two pinned `RefIdent` constructors. Declaration order matters: Lean's
/// derived `Ord` places `const` before `fvar`, then compares constructor
/// arguments from left to right.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum IleanRefIdent {
    Const { module: String, name: String },
    FVar { module: String, id: String },
}

/// A compact source location. The fifth JSON item is omitted when there is no
/// parent declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IleanLocation {
    pub start_line: u64,
    pub start_character: u64,
    pub end_line: u64,
    pub end_character: u64,
    pub parent_decl: Option<String>,
}

/// Definition and usage sites for one reference identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IleanRefInfo {
    pub definition: Option<IleanLocation>,
    pub usages: Vec<IleanLocation>,
}

/// The eight inlined declaration/selection-range coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IleanDeclInfo {
    pub range_start_line: u64,
    pub range_start_character: u64,
    pub range_end_line: u64,
    pub range_end_character: u64,
    pub selection_start_line: u64,
    pub selection_start_character: u64,
    pub selection_end_line: u64,
    pub selection_end_character: u64,
}

/// Complete pinned-epoch `.ilean` semantic value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ilean {
    pub version: u64,
    pub module: String,
    pub direct_imports: Vec<IleanImport>,
    pub references: BTreeMap<IleanRefIdent, IleanRefInfo>,
    pub decls: BTreeMap<String, IleanDeclInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum JsonValue {
    Null,
    Bool(bool),
    Nat(u64),
    String(String),
    Array(Vec<JsonValue>),
    Object(BTreeMap<String, JsonValue>),
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    cursor: usize,
    budget: IleanBudget,
    values: usize,
}

impl<'a> JsonParser<'a> {
    fn new(bytes: &'a [u8], budget: IleanBudget) -> IResult<Self> {
        if bytes.len() > budget.max_bytes {
            return Err(IleanError::Budget {
                resource: "input bytes",
                limit: budget.max_bytes,
            });
        }
        Ok(Self {
            bytes,
            cursor: 0,
            budget,
            values: 0,
        })
    }

    #[cfg(test)]
    fn parse(self) -> IResult<JsonValue> {
        self.parse_counted().map(|(value, _)| value)
    }

    fn parse_counted(mut self) -> IResult<(JsonValue, usize)> {
        self.whitespace();
        let value = self.value(0)?;
        self.whitespace();
        if self.cursor != self.bytes.len() {
            return self.syntax("trailing bytes after the root value");
        }
        Ok((value, self.values))
    }

    fn syntax<T>(&self, reason: &'static str) -> IResult<T> {
        Err(IleanError::Syntax {
            offset: self.cursor,
            reason,
        })
    }

    fn whitespace(&mut self) {
        while self
            .bytes
            .get(self.cursor)
            .is_some_and(|byte| matches!(byte, b' ' | b'\n' | b'\r' | b'\t'))
        {
            self.cursor += 1;
        }
    }

    fn charge_value(&mut self) -> IResult<()> {
        self.values = self.values.checked_add(1).ok_or(IleanError::Budget {
            resource: "JSON values",
            limit: self.budget.max_values,
        })?;
        if self.values > self.budget.max_values {
            return Err(IleanError::Budget {
                resource: "JSON values",
                limit: self.budget.max_values,
            });
        }
        Ok(())
    }

    fn value(&mut self, depth: usize) -> IResult<JsonValue> {
        if depth > self.budget.max_depth {
            return Err(IleanError::Budget {
                resource: "JSON depth",
                limit: self.budget.max_depth,
            });
        }
        self.charge_value()?;
        self.whitespace();
        match self.bytes.get(self.cursor).copied() {
            Some(b'n') => {
                self.literal(b"null")?;
                Ok(JsonValue::Null)
            }
            Some(b't') => {
                self.literal(b"true")?;
                Ok(JsonValue::Bool(true))
            }
            Some(b'f') => {
                self.literal(b"false")?;
                Ok(JsonValue::Bool(false))
            }
            Some(b'"') => self.string().map(JsonValue::String),
            Some(b'[') => self.array(depth),
            Some(b'{') => self.object(depth),
            Some(b'0'..=b'9') => self.nat().map(JsonValue::Nat),
            Some(b'-') => self.syntax("negative values are not valid Lean Nat fields"),
            Some(_) => self.syntax("unexpected value token"),
            None => self.syntax("unexpected end of input"),
        }
    }

    fn literal(&mut self, literal: &[u8]) -> IResult<()> {
        let end = self
            .cursor
            .checked_add(literal.len())
            .ok_or(IleanError::Syntax {
                offset: self.cursor,
                reason: "literal offset overflow",
            })?;
        if self.bytes.get(self.cursor..end) != Some(literal) {
            return self.syntax("malformed JSON literal");
        }
        self.cursor = end;
        Ok(())
    }

    fn nat(&mut self) -> IResult<u64> {
        let start = self.cursor;
        if self.bytes[self.cursor] == b'0' {
            self.cursor += 1;
            if self.bytes.get(self.cursor).is_some_and(u8::is_ascii_digit) {
                return self.syntax("integer has a leading zero");
            }
            return Ok(0);
        }
        let mut value = 0u64;
        while let Some(digit @ b'0'..=b'9') = self.bytes.get(self.cursor).copied() {
            value = value
                .checked_mul(10)
                .and_then(|number| number.checked_add(u64::from(digit - b'0')))
                .ok_or(IleanError::Syntax {
                    offset: start,
                    reason: "integer exceeds the supported Nat range",
                })?;
            self.cursor += 1;
        }
        if self.cursor == start {
            return self.syntax("expected an integer");
        }
        if self
            .bytes
            .get(self.cursor)
            .is_some_and(|byte| matches!(byte, b'.' | b'e' | b'E'))
        {
            return self.syntax("non-integral JSON number in a Lean Nat field");
        }
        Ok(value)
    }

    fn hex_quad(&mut self) -> IResult<u16> {
        let start = self.cursor;
        let end = start.checked_add(4).ok_or(IleanError::Syntax {
            offset: start,
            reason: "Unicode escape offset overflow",
        })?;
        let Some(digits) = self.bytes.get(start..end) else {
            return self.syntax("truncated Unicode escape");
        };
        let mut value = 0u16;
        for digit in digits {
            value *= 16;
            value += match digit {
                b'0'..=b'9' => u16::from(digit - b'0'),
                b'a'..=b'f' => u16::from(digit - b'a' + 10),
                b'A'..=b'F' => u16::from(digit - b'A' + 10),
                _ => {
                    self.cursor = start;
                    return self.syntax("invalid Unicode escape");
                }
            };
        }
        self.cursor = end;
        Ok(value)
    }

    fn string(&mut self) -> IResult<String> {
        if self.bytes.get(self.cursor) != Some(&b'"') {
            return self.syntax("expected a JSON string");
        }
        self.cursor += 1;
        let mut decoded = Vec::new();
        loop {
            let Some(byte) = self.bytes.get(self.cursor).copied() else {
                return self.syntax("unterminated JSON string");
            };
            match byte {
                b'"' => {
                    self.cursor += 1;
                    return String::from_utf8(decoded).map_err(|_| IleanError::Syntax {
                        offset: self.cursor,
                        reason: "JSON string is not valid UTF-8",
                    });
                }
                0x00..=0x1f => return self.syntax("unescaped control byte in JSON string"),
                b'\\' => {
                    self.cursor += 1;
                    let Some(escape) = self.bytes.get(self.cursor).copied() else {
                        return self.syntax("truncated JSON escape");
                    };
                    self.cursor += 1;
                    match escape {
                        b'"' => decoded.push(b'"'),
                        b'\\' => decoded.push(b'\\'),
                        b'/' => decoded.push(b'/'),
                        b'b' => decoded.push(0x08),
                        b'f' => decoded.push(0x0c),
                        b'n' => decoded.push(b'\n'),
                        b'r' => decoded.push(b'\r'),
                        b't' => decoded.push(b'\t'),
                        b'u' => {
                            let first = self.hex_quad()?;
                            let scalar = if (0xd800..=0xdbff).contains(&first) {
                                if self.bytes.get(self.cursor..self.cursor + 2) != Some(br"\u") {
                                    return self.syntax(
                                        "high surrogate is not followed by a Unicode escape",
                                    );
                                }
                                self.cursor += 2;
                                let second = self.hex_quad()?;
                                if !(0xdc00..=0xdfff).contains(&second) {
                                    return self.syntax(
                                        "high surrogate is not followed by a low surrogate",
                                    );
                                }
                                0x1_0000
                                    + ((u32::from(first) - 0xd800) << 10)
                                    + (u32::from(second) - 0xdc00)
                            } else if (0xdc00..=0xdfff).contains(&first) {
                                return self.syntax("unpaired low surrogate");
                            } else {
                                u32::from(first)
                            };
                            let character = char::from_u32(scalar).ok_or(IleanError::Syntax {
                                offset: self.cursor,
                                reason: "Unicode escape is not a scalar value",
                            })?;
                            let mut utf8 = [0u8; 4];
                            decoded.extend_from_slice(character.encode_utf8(&mut utf8).as_bytes());
                        }
                        _ => return self.syntax("unknown JSON escape"),
                    }
                }
                _ => {
                    decoded.push(byte);
                    self.cursor += 1;
                }
            }
            if decoded.len() > self.budget.max_bytes {
                return Err(IleanError::Budget {
                    resource: "decoded string bytes",
                    limit: self.budget.max_bytes,
                });
            }
        }
    }

    fn array(&mut self, depth: usize) -> IResult<JsonValue> {
        self.cursor += 1;
        self.whitespace();
        let mut values = Vec::new();
        if self.bytes.get(self.cursor) == Some(&b']') {
            self.cursor += 1;
            return Ok(JsonValue::Array(values));
        }
        loop {
            values.push(self.value(depth + 1)?);
            self.whitespace();
            match self.bytes.get(self.cursor) {
                Some(b',') => {
                    self.cursor += 1;
                    self.whitespace();
                }
                Some(b']') => {
                    self.cursor += 1;
                    return Ok(JsonValue::Array(values));
                }
                _ => return self.syntax("array item is not followed by ',' or ']'"),
            }
        }
    }

    fn object(&mut self, depth: usize) -> IResult<JsonValue> {
        self.cursor += 1;
        self.whitespace();
        let mut fields = BTreeMap::new();
        if self.bytes.get(self.cursor) == Some(&b'}') {
            self.cursor += 1;
            return Ok(JsonValue::Object(fields));
        }
        loop {
            let key = self.string()?;
            self.whitespace();
            if self.bytes.get(self.cursor) != Some(&b':') {
                return self.syntax("object key is not followed by ':'");
            }
            self.cursor += 1;
            let value = self.value(depth + 1)?;
            if fields.insert(key, value).is_some() {
                return self.syntax("duplicate object key");
            }
            self.whitespace();
            match self.bytes.get(self.cursor) {
                Some(b',') => {
                    self.cursor += 1;
                    self.whitespace();
                }
                Some(b'}') => {
                    self.cursor += 1;
                    return Ok(JsonValue::Object(fields));
                }
                _ => return self.syntax("object field is not followed by ',' or '}'"),
            }
        }
    }
}

fn shape<T>(context: &'static str, reason: &'static str) -> IResult<T> {
    Err(IleanError::Shape { context, reason })
}

fn object(value: JsonValue, context: &'static str) -> IResult<BTreeMap<String, JsonValue>> {
    match value {
        JsonValue::Object(fields) => Ok(fields),
        _ => shape(context, "expected an object"),
    }
}

fn array(value: JsonValue, context: &'static str) -> IResult<Vec<JsonValue>> {
    match value {
        JsonValue::Array(values) => Ok(values),
        _ => shape(context, "expected an array"),
    }
}

fn string(value: JsonValue, context: &'static str) -> IResult<String> {
    match value {
        JsonValue::String(value) => Ok(value),
        _ => shape(context, "expected a string"),
    }
}

fn boolean(value: JsonValue, context: &'static str) -> IResult<bool> {
    match value {
        JsonValue::Bool(value) => Ok(value),
        _ => shape(context, "expected a Boolean"),
    }
}

fn nat(value: JsonValue, context: &'static str) -> IResult<u64> {
    match value {
        JsonValue::Nat(value) => Ok(value),
        _ => shape(context, "expected a Nat"),
    }
}

fn required(
    fields: &mut BTreeMap<String, JsonValue>,
    name: &str,
    context: &'static str,
) -> IResult<JsonValue> {
    fields.remove(name).ok_or(IleanError::Shape {
        context,
        reason: "required field is absent",
    })
}

fn no_extra(fields: &BTreeMap<String, JsonValue>, context: &'static str) -> IResult<()> {
    if fields.is_empty() {
        Ok(())
    } else {
        shape(context, "unknown or duplicate semantic field")
    }
}

fn validate_generated_fields() -> IResult<()> {
    let actual: Vec<&str> = format::ILEAN_FIELDS
        .iter()
        .map(|field| field.name)
        .collect();
    if actual != ["version", "module", "directImports", "references", "decls"] {
        return shape(
            "generated contract",
            "Ilean field inventory differs from the codec",
        );
    }
    if format::ILEAN_FIELDS[0].default != Some("5") {
        return shape(
            "generated contract",
            "Ilean version default differs from the codec",
        );
    }
    Ok(())
}

fn parse_import(value: JsonValue) -> IResult<IleanImport> {
    let values = array(value, "direct import")?;
    let [module, is_private, is_all, is_meta]: [JsonValue; 4] =
        values.try_into().map_err(|_| IleanError::Shape {
            context: "direct import",
            reason: "expected four compact fields",
        })?;
    Ok(IleanImport {
        module: string(module, "direct import module")?,
        is_private: boolean(is_private, "direct import private flag")?,
        is_all: boolean(is_all, "direct import all flag")?,
        is_meta: boolean(is_meta, "direct import meta flag")?,
    })
}

fn parse_decl(value: JsonValue) -> IResult<IleanDeclInfo> {
    let values = array(value, "declaration info")?;
    let [
        range_start_line,
        range_start_character,
        range_end_line,
        range_end_character,
        selection_start_line,
        selection_start_character,
        selection_end_line,
        selection_end_character,
    ]: [JsonValue; 8] = values.try_into().map_err(|_| IleanError::Shape {
        context: "declaration info",
        reason: "expected eight compact coordinates",
    })?;
    Ok(IleanDeclInfo {
        range_start_line: nat(range_start_line, "declaration range start line")?,
        range_start_character: nat(range_start_character, "declaration range start character")?,
        range_end_line: nat(range_end_line, "declaration range end line")?,
        range_end_character: nat(range_end_character, "declaration range end character")?,
        selection_start_line: nat(selection_start_line, "selection range start line")?,
        selection_start_character: nat(
            selection_start_character,
            "selection range start character",
        )?,
        selection_end_line: nat(selection_end_line, "selection range end line")?,
        selection_end_character: nat(selection_end_character, "selection range end character")?,
    })
}

fn parse_location(value: JsonValue) -> IResult<IleanLocation> {
    let mut values = array(value, "reference location")?;
    if values.len() != 4 && values.len() != 5 {
        return shape(
            "reference location",
            "expected four coordinates and an optional parent declaration",
        );
    }
    let parent_decl = if values.len() == 5 {
        Some(string(
            values.pop().ok_or(IleanError::Shape {
                context: "reference location",
                reason: "optional parent declaration is absent",
            })?,
            "reference parent declaration",
        )?)
    } else {
        None
    };
    let [start_line, start_character, end_line, end_character]: [JsonValue; 4] =
        values.try_into().map_err(|_| IleanError::Shape {
            context: "reference location",
            reason: "coordinate count changed during decoding",
        })?;
    Ok(IleanLocation {
        start_line: nat(start_line, "reference start line")?,
        start_character: nat(start_character, "reference start character")?,
        end_line: nat(end_line, "reference end line")?,
        end_character: nat(end_character, "reference end character")?,
        parent_decl,
    })
}

fn parse_ref_info(value: JsonValue) -> IResult<IleanRefInfo> {
    let mut fields = object(value, "reference info")?;
    let definition = match required(&mut fields, "definition", "reference info")? {
        JsonValue::Null => None,
        value => Some(parse_location(value)?),
    };
    let usages = array(
        required(&mut fields, "usages", "reference info")?,
        "reference usages",
    )?
    .into_iter()
    .map(parse_location)
    .collect::<IResult<Vec<_>>>()?;
    no_extra(&fields, "reference info")?;
    Ok(IleanRefInfo { definition, usages })
}

fn parse_ref_ident(value: &str, budget: IleanBudget) -> IResult<(IleanRefIdent, usize)> {
    let (parsed, values) = JsonParser::new(value.as_bytes(), budget)?.parse_counted()?;
    let mut outer = object(parsed, "reference identifier")?;
    if outer.len() != 1 {
        return shape("reference identifier", "expected exactly one constructor");
    }
    if let Some(value) = outer.remove("c") {
        let mut fields = object(value, "constant reference identifier")?;
        let module = string(
            required(&mut fields, "m", "constant reference identifier")?,
            "constant reference module",
        )?;
        let name = string(
            required(&mut fields, "n", "constant reference identifier")?,
            "constant reference name",
        )?;
        no_extra(&fields, "constant reference identifier")?;
        return Ok((IleanRefIdent::Const { module, name }, values));
    }
    if let Some(value) = outer.remove("f") {
        let mut fields = object(value, "free-variable reference identifier")?;
        let module = string(
            required(&mut fields, "m", "free-variable reference identifier")?,
            "free-variable reference module",
        )?;
        let id = string(
            required(&mut fields, "i", "free-variable reference identifier")?,
            "free-variable reference id",
        )?;
        no_extra(&fields, "free-variable reference identifier")?;
        return Ok((IleanRefIdent::FVar { module, id }, values));
    }
    shape(
        "reference identifier",
        "unknown reference identifier constructor",
    )
}

/// Decode one `.ilean` file under explicit byte/value/depth limits.
pub fn decode_ilean(bytes: &[u8], budget: IleanBudget) -> IResult<Ilean> {
    validate_generated_fields()?;
    let (parsed, mut visited_values) = JsonParser::new(bytes, budget)?.parse_counted()?;
    let mut fields = object(parsed, "root")?;
    let version = match fields.remove("version") {
        Some(value) => nat(value, "version")?,
        None => format::ILEAN_VERSION,
    };
    if version != format::ILEAN_VERSION {
        return Err(IleanError::UnknownVersion {
            found: version,
            expected: format::ILEAN_VERSION,
        });
    }
    let module = string(required(&mut fields, "module", "root")?, "module")?;
    let direct_imports = array(
        required(&mut fields, "directImports", "root")?,
        "direct imports",
    )?
    .into_iter()
    .map(parse_import)
    .collect::<IResult<Vec<_>>>()?;

    let mut references = BTreeMap::new();
    for (key, value) in object(required(&mut fields, "references", "root")?, "references")? {
        let (ident, key_values) = parse_ref_ident(&key, budget)?;
        visited_values = visited_values
            .checked_add(key_values)
            .ok_or(IleanError::Budget {
                resource: "JSON values",
                limit: budget.max_values,
            })?;
        if visited_values > budget.max_values {
            return Err(IleanError::Budget {
                resource: "JSON values",
                limit: budget.max_values,
            });
        }
        if references.insert(ident, parse_ref_info(value)?).is_some() {
            return shape(
                "references",
                "two JSON keys decode to one reference identifier",
            );
        }
    }

    let mut decls = BTreeMap::new();
    for (name, value) in object(required(&mut fields, "decls", "root")?, "declarations")? {
        decls.insert(name, parse_decl(value)?);
    }
    no_extra(&fields, "root")?;
    Ok(Ilean {
        version,
        module,
        direct_imports,
        references,
        decls,
    })
}

struct JsonWriter {
    output: Vec<u8>,
    limit: usize,
}

impl JsonWriter {
    fn new(limit: usize) -> Self {
        Self {
            output: Vec::new(),
            limit,
        }
    }

    fn reserve(&self, bytes: usize) -> IResult<()> {
        if self
            .output
            .len()
            .checked_add(bytes)
            .is_none_or(|total| total > self.limit)
        {
            return Err(IleanError::Budget {
                resource: "output bytes",
                limit: self.limit,
            });
        }
        Ok(())
    }

    fn raw(&mut self, value: &str) -> IResult<()> {
        self.reserve(value.len())?;
        self.output.extend_from_slice(value.as_bytes());
        Ok(())
    }

    fn byte(&mut self, value: u8) -> IResult<()> {
        self.reserve(1)?;
        self.output.push(value);
        Ok(())
    }

    fn nat(&mut self, value: u64) -> IResult<()> {
        self.raw(&value.to_string())
    }

    fn boolean(&mut self, value: bool) -> IResult<()> {
        self.raw(if value { "true" } else { "false" })
    }

    fn string(&mut self, value: &str) -> IResult<()> {
        self.byte(b'"')?;
        for character in value.chars() {
            match character {
                '"' => self.raw("\\\"")?,
                '\\' => self.raw("\\\\")?,
                '\u{08}' => self.raw("\\b")?,
                '\u{0c}' => self.raw("\\f")?,
                '\n' => self.raw("\\n")?,
                '\r' => self.raw("\\r")?,
                '\t' => self.raw("\\t")?,
                '\u{00}'..='\u{1f}' => {
                    self.raw("\\u00")?;
                    let value = character as u8;
                    const HEX: &[u8; 16] = b"0123456789abcdef";
                    self.byte(HEX[usize::from(value >> 4)])?;
                    self.byte(HEX[usize::from(value & 0x0f)])?;
                }
                _ => {
                    let mut utf8 = [0u8; 4];
                    self.raw(character.encode_utf8(&mut utf8))?;
                }
            }
        }
        self.byte(b'"')
    }
}

fn write_location(writer: &mut JsonWriter, location: &IleanLocation) -> IResult<()> {
    writer.byte(b'[')?;
    writer.nat(location.start_line)?;
    writer.byte(b',')?;
    writer.nat(location.start_character)?;
    writer.byte(b',')?;
    writer.nat(location.end_line)?;
    writer.byte(b',')?;
    writer.nat(location.end_character)?;
    if let Some(parent) = &location.parent_decl {
        if parent.is_empty() {
            return shape(
                "reference location",
                "an empty parent declaration is the omitted representation",
            );
        }
        writer.byte(b',')?;
        writer.string(parent)?;
    }
    writer.byte(b']')
}

fn write_ref_ident(ident: &IleanRefIdent, limit: usize) -> IResult<String> {
    let mut writer = JsonWriter::new(limit);
    match ident {
        IleanRefIdent::Const { module, name } => {
            writer.raw("{\"c\":{\"m\":")?;
            writer.string(module)?;
            writer.raw(",\"n\":")?;
            writer.string(name)?;
            writer.raw("}}")?;
        }
        IleanRefIdent::FVar { module, id } => {
            writer.raw("{\"f\":{\"i\":")?;
            writer.string(id)?;
            writer.raw(",\"m\":")?;
            writer.string(module)?;
            writer.raw("}}")?;
        }
    }
    String::from_utf8(writer.output).map_err(|_| IleanError::Shape {
        context: "reference identifier",
        reason: "encoder produced non-UTF-8",
    })
}

fn write_ref_info(writer: &mut JsonWriter, info: &IleanRefInfo) -> IResult<()> {
    writer.raw("{\"definition\":")?;
    if let Some(definition) = &info.definition {
        write_location(writer, definition)?;
    } else {
        writer.raw("null")?;
    }
    writer.raw(",\"usages\":[")?;
    for (index, usage) in info.usages.iter().enumerate() {
        if index != 0 {
            writer.byte(b',')?;
        }
        write_location(writer, usage)?;
    }
    writer.raw("]}")
}

fn write_decl(writer: &mut JsonWriter, info: IleanDeclInfo) -> IResult<()> {
    writer.byte(b'[')?;
    for (index, coordinate) in [
        info.range_start_line,
        info.range_start_character,
        info.range_end_line,
        info.range_end_character,
        info.selection_start_line,
        info.selection_start_character,
        info.selection_end_line,
        info.selection_end_character,
    ]
    .into_iter()
    .enumerate()
    {
        if index != 0 {
            writer.byte(b',')?;
        }
        writer.nat(coordinate)?;
    }
    writer.byte(b']')
}

/// Encode one semantic value in the pinned Reference's compact deterministic
/// JSON form. Reference-produced inputs satisfy
/// `encode_ilean(decode_ilean(bytes)) == bytes`.
pub fn encode_ilean(value: &Ilean, budget: IleanBudget) -> IResult<Vec<u8>> {
    validate_generated_fields()?;
    if value.version != format::ILEAN_VERSION {
        return Err(IleanError::UnknownVersion {
            found: value.version,
            expected: format::ILEAN_VERSION,
        });
    }
    let mut writer = JsonWriter::new(budget.max_bytes);
    writer.raw("{\"decls\":{")?;
    for (index, (name, info)) in value.decls.iter().enumerate() {
        if index != 0 {
            writer.byte(b',')?;
        }
        writer.string(name)?;
        writer.byte(b':')?;
        write_decl(&mut writer, *info)?;
    }
    writer.raw("},\"directImports\":[")?;
    for (index, import) in value.direct_imports.iter().enumerate() {
        if index != 0 {
            writer.byte(b',')?;
        }
        writer.byte(b'[')?;
        writer.string(&import.module)?;
        writer.byte(b',')?;
        writer.boolean(import.is_private)?;
        writer.byte(b',')?;
        writer.boolean(import.is_all)?;
        writer.byte(b',')?;
        writer.boolean(import.is_meta)?;
        writer.byte(b']')?;
    }
    writer.raw("],\"module\":")?;
    writer.string(&value.module)?;
    writer.raw(",\"references\":{")?;
    // `ModuleRefs.toJson` first renders each `RefIdent` as a JSON string and
    // then feeds those strings to `Json.mkObj`. The JSON object's String
    // ordering is therefore authoritative here, not `RefIdent`'s semantic
    // ordering. They differ at prefixes: `Array.set!` sorts before
    // `Array.set` because `!` precedes the latter key's escaped closing quote.
    let mut references = Vec::with_capacity(value.references.len());
    let mut reference_key_bytes = 0usize;
    for (ident, info) in &value.references {
        let ident = write_ref_ident(ident, budget.max_bytes)?;
        reference_key_bytes =
            reference_key_bytes
                .checked_add(ident.len())
                .ok_or(IleanError::Budget {
                    resource: "output bytes",
                    limit: budget.max_bytes,
                })?;
        if reference_key_bytes > budget.max_bytes {
            return Err(IleanError::Budget {
                resource: "output bytes",
                limit: budget.max_bytes,
            });
        }
        references.push((ident, info));
    }
    references.sort_by(|left, right| left.0.cmp(&right.0));
    if references.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return shape(
            "references",
            "two reference identifiers encode to one JSON object key",
        );
    }
    for (index, (ident, info)) in references.iter().enumerate() {
        if index != 0 {
            writer.byte(b',')?;
        }
        writer.string(ident)?;
        writer.byte(b':')?;
        write_ref_info(&mut writer, info)?;
    }
    writer.raw("},\"version\":")?;
    writer.nat(value.version)?;
    writer.byte(b'}')?;
    Ok(writer.output)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_fixture(input: &str) -> IResult<Ilean> {
        decode_ilean(input.as_bytes(), IleanBudget::default())
    }

    #[test]
    fn malformed_unknown_and_over_budget_inputs_refuse_typed() {
        assert!(matches!(
            parse_fixture("{"),
            Err(IleanError::Syntax {
                reason: "expected a JSON string",
                ..
            })
        ));
        assert!(matches!(
            parse_fixture(
                "{\"decls\":{},\"directImports\":[],\"module\":\"M\",\
                 \"references\":{},\"version\":6}"
            ),
            Err(IleanError::UnknownVersion {
                found: 6,
                expected: 5
            })
        ));
        assert!(matches!(
            decode_ilean(
                br#"{"decls":{},"directImports":[],"module":"M","references":{},"version":5}"#,
                IleanBudget {
                    max_bytes: 8,
                    ..IleanBudget::default()
                }
            ),
            Err(IleanError::Budget {
                resource: "input bytes",
                limit: 8
            })
        ));
        assert!(matches!(
            decode_ilean(
                br#"{"decls":{},"directImports":[],"module":"M","references":{},"version":5}"#,
                IleanBudget {
                    max_values: 1,
                    ..IleanBudget::default()
                }
            ),
            Err(IleanError::Budget {
                resource: "JSON values",
                limit: 1
            })
        ));
    }

    #[test]
    fn duplicate_keys_surrogates_and_noncanonical_locations_refuse() {
        assert!(matches!(
            parse_fixture(
                "{\"decls\":{},\"decls\":{},\"directImports\":[],\"module\":\"M\",\
                 \"references\":{},\"version\":5}"
            ),
            Err(IleanError::Syntax {
                reason: "duplicate object key",
                ..
            })
        ));
        assert!(matches!(
            JsonParser::new(br#""\ud800x""#, IleanBudget::default())
                .expect("budget")
                .parse(),
            Err(IleanError::Syntax {
                reason: "high surrogate is not followed by a Unicode escape",
                ..
            })
        ));
        let mut value = parse_fixture(
            "{\"decls\":{},\"directImports\":[],\"module\":\"M\",\
             \"references\":{},\"version\":5}",
        )
        .expect("minimal Ilean");
        value.references.insert(
            IleanRefIdent::Const {
                module: "M".to_string(),
                name: "x".to_string(),
            },
            IleanRefInfo {
                definition: Some(IleanLocation {
                    start_line: 0,
                    start_character: 0,
                    end_line: 0,
                    end_character: 1,
                    parent_decl: Some(String::new()),
                }),
                usages: Vec::new(),
            },
        );
        assert!(matches!(
            encode_ilean(&value, IleanBudget::default()),
            Err(IleanError::Shape {
                context: "reference location",
                reason: "an empty parent declaration is the omitted representation"
            })
        ));
    }

    #[test]
    fn hostile_nesting_hits_the_depth_budget_on_a_small_stack() {
        let input = format!("{}0{}", "[".repeat(2_000), "]".repeat(2_000));
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || {
                assert!(matches!(
                    JsonParser::new(
                        input.as_bytes(),
                        IleanBudget {
                            max_depth: 32,
                            ..IleanBudget::default()
                        }
                    )
                    .expect("byte budget")
                    .parse(),
                    Err(IleanError::Budget {
                        resource: "JSON depth",
                        limit: 32
                    })
                ));
            })
            .expect("spawn small-stack decoder")
            .join()
            .expect("small-stack decoder");
    }

    #[test]
    fn free_variable_reference_keys_use_the_pinned_compact_shape() {
        assert_eq!(
            write_ref_ident(
                &IleanRefIdent::FVar {
                    module: "M".to_string(),
                    id: "i".to_string(),
                },
                1024,
            )
            .expect("encode fvar key"),
            "{\"f\":{\"i\":\"i\",\"m\":\"M\"}}"
        );
    }

    #[test]
    fn encoded_reference_key_order_not_semantic_prefix_order_is_pinned() {
        let mut value = parse_fixture(
            "{\"decls\":{},\"directImports\":[],\"module\":\"M\",\
             \"references\":{},\"version\":5}",
        )
        .expect("minimal Ilean");
        for name in ["Array.set", "Array.set!"] {
            value.references.insert(
                IleanRefIdent::Const {
                    module: "M".to_string(),
                    name: name.to_string(),
                },
                IleanRefInfo {
                    definition: None,
                    usages: Vec::new(),
                },
            );
        }
        let encoded = String::from_utf8(
            encode_ilean(&value, IleanBudget::default()).expect("encode ordered references"),
        )
        .expect("JSON is UTF-8");
        let bang = encoded.find("Array.set!").expect("bang reference");
        let prefix = encoded
            .match_indices("Array.set")
            .map(|(index, _)| index)
            .find(|index| *index != bang)
            .expect("prefix reference");
        assert!(bang < prefix);
    }
}
