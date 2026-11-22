//! Pin-extracted builtin parser combinator-AST table
//! (Step 2a of `fln-generated-builtin-grammar-spike-kcvj`, Rules D1/D5/D8-2).
//!
//! Loads `contracts/REFERENCE_BUILTIN_PARSER_TABLE.jsonl` — mechanically extracted
//! from the pinned Reference toolchain by `scripts/extract/gen_builtin_parser_table.sh` —
//! without external dependencies (closed dependency universe D1) and validates:
//!
//! 1. schema version and declared vs. actual row counts;
//! 2. uniqueness of every primitive and generatable declaration name;
//! 3. closure totality: every `Lean.Parser.*` symbol referenced in any generatable
//!    combinator AST resolves to a classified primitive, a generatable definition,
//!    or the explicit set of non-parser constants (`maxPrec`, `leadPrec`, …);
//! 4. deterministic per-category leading/trailing registration tables for all 10
//!    builtin categories (`attr`, `command`, `doElem`, `level`, `prec`, `prio`,
//!    `structInstFieldDecl`, `stx`, `tactic`, `term`).

use fln_core::name::Name;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::OnceLock;

/// Checked-in builtin parser combinator-AST table extracted from the pinned Reference.
pub const BUILTIN_PARSER_TABLE: &str =
    include_str!("../../../contracts/REFERENCE_BUILTIN_PARSER_TABLE.jsonl");

/// Expected schema tag in row 1.
pub const BUILTIN_PARSER_TABLE_SCHEMA: &str = "fln.builtin-parser-table/1";

/// Maximum JSON/AST nesting depth accepted while loading a table (FL-INV-07).
const MAX_JSON_DEPTH: usize = 128;

/// Non-parser `Lean.Parser.*` constants legally referenced by generatable parser bodies
/// (precedence constants, cache context projections, and pure identifier predicates).
const KNOWN_NON_PARSER_LP_CONSTS: &[&str] = &[
    "Lean.Parser.maxPrec",
    "Lean.Parser.leadPrec",
    "Lean.Parser.argPrec",
    "Lean.Parser.minPrec",
    "Lean.Parser.CacheableParserContext.prec",
    "Lean.Parser.CacheableParserContext.quotDepth",
    "Lean.Parser.CacheableParserContext.suppressInsideQuot",
    "Lean.Parser.CacheableParserContext.savedPos?",
    "Lean.Parser.CacheableParserContext.forbiddenTk?",
    "Lean.Parser.Token",
    "Lean.Parser.TrailingParser",
    "Lean.Parser.Term.isIdent",
    "Lean.Parser.Term.isIdentOrDotIdentOrProj",
    "Lean.Parser.instAndThenParser",
    "Lean.Parser.instOrElseParser",
];

/// Why a builtin parser table failed to parse or validate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltinTableError {
    Empty,
    Schema {
        found: String,
    },
    Json {
        line: usize,
        detail: String,
    },
    MalformedRow {
        line: usize,
        detail: String,
    },
    DuplicateName {
        line: usize,
        name: String,
    },
    CountMismatch {
        field: &'static str,
        declared: usize,
        found: usize,
    },
    UnresolvedParserRef {
        owner: String,
        target: String,
    },
}

impl fmt::Display for BuiltinTableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "builtin parser table is empty"),
            Self::Schema { found } => write!(
                f,
                "expected schema {BUILTIN_PARSER_TABLE_SCHEMA}, found {found:?}"
            ),
            Self::Json { line, detail } => write!(f, "line {line}: invalid JSON: {detail}"),
            Self::MalformedRow { line, detail } => write!(f, "line {line}: {detail}"),
            Self::DuplicateName { line, name } => {
                write!(f, "line {line}: duplicate declaration {name:?}")
            }
            Self::CountMismatch {
                field,
                declared,
                found,
            } => write!(
                f,
                "header count mismatch for {field}: declared {declared}, found {found}"
            ),
            Self::UnresolvedParserRef { owner, target } => write!(
                f,
                "generatable entry {owner:?} references unclassified Lean.Parser constant {target:?}"
            ),
        }
    }
}

impl std::error::Error for BuiltinTableError {}

/// Header metadata from row 1 of `REFERENCE_BUILTIN_PARSER_TABLE.jsonl`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableHeader {
    pub lean_version: String,
    pub githash: String,
    pub closure_size: usize,
    pub total_parsers: usize,
    pub generatable_parsers: usize,
    pub primitive_parsers: usize,
    pub generatable_helpers: usize,
    pub primitive_total: usize,
    pub direct_prim: usize,
    pub fn_helper_prim: usize,
    pub non_defn_prim: usize,
}

/// Classification of one primitive-floor entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimitiveRole {
    ParserDef,
    Combinator,
    FnHelper,
    TypeOrCtor,
}

/// Classification of one generatable entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GeneratableRole {
    ParserDef,
    Helper,
}

/// One `_regBuiltin` attachment of a parser declaration to a syntax category.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BuiltinRegistration {
    pub category: Name,
    pub leading: bool,
    pub priority: u32,
}

/// One primitive-floor row in the extracted table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrimitiveEntry {
    pub name: Name,
    pub role: PrimitiveRole,
    pub is_trailing: bool,
    pub type_arity: usize,
    pub registrations: Vec<BuiltinRegistration>,
    pub used_lean_parser: Vec<Name>,
}

/// Normalized combinator AST of one generatable `Lean.Parser.*` definition or helper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinatorAst {
    Seq(Box<CombinatorAst>, Box<CombinatorAst>),
    OrElse(Box<CombinatorAst>, Box<CombinatorAst>),
    Call {
        func: Name,
        args: Vec<CombinatorAst>,
    },
    App {
        func: Box<CombinatorAst>,
        args: Vec<CombinatorAst>,
    },
    Lam {
        param: String,
        body: Box<CombinatorAst>,
    },
    Let {
        name: String,
        val: Box<CombinatorAst>,
        body: Box<CombinatorAst>,
    },
    Ite {
        cond: Box<CombinatorAst>,
        then_branch: Box<CombinatorAst>,
        else_branch: Box<CombinatorAst>,
    },
    SomeVal(Box<CombinatorAst>),
    NoneVal,
    Append(Box<CombinatorAst>, Box<CombinatorAst>),
    Beq(Box<CombinatorAst>, Box<CombinatorAst>),
    BoolOr(Box<CombinatorAst>, Box<CombinatorAst>),
    Const(Name),
    Var {
        name: String,
        idx: usize,
    },
    LitNat(u64),
    LitStr(String),
    LitName(Name),
    LitBool(bool),
    LitChar(u32),
    LitList(Vec<CombinatorAst>),
}

/// One generatable parser definition or helper function in the extracted table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratableEntry {
    pub name: Name,
    pub role: GeneratableRole,
    pub is_trailing: bool,
    pub params: Vec<String>,
    pub registrations: Vec<BuiltinRegistration>,
    pub ast: CombinatorAst,
}

/// One registered parser entry in a category dispatch table.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CategoryEntry {
    pub decl: Name,
    pub priority: u32,
    pub is_primitive: bool,
}

/// Leading and trailing builtin parser registrations for one syntax category.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CategoryRegistrations {
    pub leading: Vec<CategoryEntry>,
    pub trailing: Vec<CategoryEntry>,
}

/// Validated in-memory representation of `REFERENCE_BUILTIN_PARSER_TABLE.jsonl`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuiltinParserTable {
    pub header: TableHeader,
    pub primitives: BTreeMap<Name, PrimitiveEntry>,
    pub generatables: BTreeMap<Name, GeneratableEntry>,
    pub categories: BTreeMap<Name, CategoryRegistrations>,
}

/// Cached parsed representation of the checked-in `BUILTIN_PARSER_TABLE`.
pub fn reference_builtin_parser_table() -> &'static BuiltinParserTable {
    static TABLE: OnceLock<BuiltinParserTable> = OnceLock::new();
    TABLE.get_or_init(|| {
        BuiltinParserTable::parse(BUILTIN_PARSER_TABLE)
            .expect("checked-in contracts/REFERENCE_BUILTIN_PARSER_TABLE.jsonl must validate")
    })
}

impl BuiltinParserTable {
    /// Parse and validate a `fln.builtin-parser-table/1` JSONL stream.
    pub fn parse(text: &str) -> Result<Self, BuiltinTableError> {
        let mut lines = text
            .lines()
            .enumerate()
            .filter(|(_, line)| !line.trim().is_empty());
        let Some((first_idx, first_line)) = lines.next() else {
            return Err(BuiltinTableError::Empty);
        };
        let header_line_no = first_idx + 1;
        let header_json = parse_json(first_line).map_err(|detail| BuiltinTableError::Json {
            line: header_line_no,
            detail,
        })?;
        let header_obj = as_obj(&header_json, header_line_no, "header must be a JSON object")?;
        let schema = req_str(header_obj, "schema", header_line_no)?;
        if schema != BUILTIN_PARSER_TABLE_SCHEMA {
            return Err(BuiltinTableError::Schema {
                found: schema.to_owned(),
            });
        }
        if req_str(header_obj, "kind", header_line_no)? != "header" {
            return Err(BuiltinTableError::MalformedRow {
                line: header_line_no,
                detail: "first row must have kind=\"header\"".to_owned(),
            });
        }
        let header = TableHeader {
            lean_version: req_str(header_obj, "lean_version", header_line_no)?.to_owned(),
            githash: req_str(header_obj, "githash", header_line_no)?.to_owned(),
            closure_size: req_usize(header_obj, "closure_size", header_line_no)?,
            total_parsers: req_usize(header_obj, "total_parsers", header_line_no)?,
            generatable_parsers: req_usize(header_obj, "generatable_parsers", header_line_no)?,
            primitive_parsers: req_usize(header_obj, "primitive_parsers", header_line_no)?,
            generatable_helpers: req_usize(header_obj, "generatable_helpers", header_line_no)?,
            primitive_total: req_usize(header_obj, "primitive_total", header_line_no)?,
            direct_prim: req_usize(header_obj, "direct_prim", header_line_no)?,
            fn_helper_prim: req_usize(header_obj, "fn_helper_prim", header_line_no)?,
            non_defn_prim: req_usize(header_obj, "non_defn_prim", header_line_no)?,
        };

        let mut primitives = BTreeMap::new();
        let mut generatables = BTreeMap::new();
        let mut categories: BTreeMap<Name, CategoryRegistrations> = BTreeMap::new();

        for (idx, line) in lines {
            let line_no = idx + 1;
            let value = parse_json(line).map_err(|detail| BuiltinTableError::Json {
                line: line_no,
                detail,
            })?;
            let obj = as_obj(&value, line_no, "row must be a JSON object")?;
            let kind = req_str(obj, "kind", line_no)?;
            match kind {
                "primitive" => {
                    let raw_name = req_str(obj, "name", line_no)?;
                    let name = parse_dotted_name(raw_name);
                    if primitives.contains_key(&name) || generatables.contains_key(&name) {
                        return Err(BuiltinTableError::DuplicateName {
                            line: line_no,
                            name: raw_name.to_owned(),
                        });
                    }
                    let role = match req_str(obj, "role", line_no)? {
                        "parser_def" => PrimitiveRole::ParserDef,
                        "combinator" => PrimitiveRole::Combinator,
                        "fn_helper" => PrimitiveRole::FnHelper,
                        "type_or_ctor" => PrimitiveRole::TypeOrCtor,
                        other => {
                            return Err(BuiltinTableError::MalformedRow {
                                line: line_no,
                                detail: format!("unknown primitive role {other:?}"),
                            });
                        }
                    };
                    let is_trailing = req_bool(obj, "is_trailing", line_no)?;
                    let type_arity = req_usize(obj, "type_arity", line_no)?;
                    let registrations = parse_registrations(obj, line_no)?;
                    let used_lean_parser = parse_name_array(obj, "used_lean_parser", line_no)?;
                    for reg in &registrations {
                        let slot = categories.entry(reg.category.clone()).or_default();
                        let entry = CategoryEntry {
                            decl: name.clone(),
                            priority: reg.priority,
                            is_primitive: true,
                        };
                        if reg.leading {
                            slot.leading.push(entry);
                        } else {
                            slot.trailing.push(entry);
                        }
                    }
                    primitives.insert(
                        name.clone(),
                        PrimitiveEntry {
                            name,
                            role,
                            is_trailing,
                            type_arity,
                            registrations,
                            used_lean_parser,
                        },
                    );
                }
                "generatable" => {
                    let raw_name = req_str(obj, "name", line_no)?;
                    let name = parse_dotted_name(raw_name);
                    if primitives.contains_key(&name) || generatables.contains_key(&name) {
                        return Err(BuiltinTableError::DuplicateName {
                            line: line_no,
                            name: raw_name.to_owned(),
                        });
                    }
                    let role = match req_str(obj, "role", line_no)? {
                        "parser_def" => GeneratableRole::ParserDef,
                        "helper" => GeneratableRole::Helper,
                        other => {
                            return Err(BuiltinTableError::MalformedRow {
                                line: line_no,
                                detail: format!("unknown generatable role {other:?}"),
                            });
                        }
                    };
                    let is_trailing = req_bool(obj, "is_trailing", line_no)?;
                    let params = parse_string_array(obj, "params", line_no)?;
                    let registrations = parse_registrations(obj, line_no)?;
                    let ast_val =
                        obj.get("ast")
                            .ok_or_else(|| BuiltinTableError::MalformedRow {
                                line: line_no,
                                detail: "missing 'ast' field".to_owned(),
                            })?;
                    let ast = parse_ast(ast_val, line_no)?;
                    for reg in &registrations {
                        let slot = categories.entry(reg.category.clone()).or_default();
                        let entry = CategoryEntry {
                            decl: name.clone(),
                            priority: reg.priority,
                            is_primitive: false,
                        };
                        if reg.leading {
                            slot.leading.push(entry);
                        } else {
                            slot.trailing.push(entry);
                        }
                    }
                    generatables.insert(
                        name.clone(),
                        GeneratableEntry {
                            name,
                            role,
                            is_trailing,
                            params,
                            registrations,
                            ast,
                        },
                    );
                }
                other => {
                    return Err(BuiltinTableError::MalformedRow {
                        line: line_no,
                        detail: format!("unknown row kind {other:?}"),
                    });
                }
            }
        }

        // Verify header counts against actual rows.
        check_count("primitive_total", header.primitive_total, primitives.len())?;
        let prim_parsers = primitives
            .values()
            .filter(|e| e.role == PrimitiveRole::ParserDef)
            .count();
        check_count("primitive_parsers", header.primitive_parsers, prim_parsers)?;
        let fn_helpers = primitives
            .values()
            .filter(|e| e.role == PrimitiveRole::FnHelper)
            .count();
        check_count("fn_helper_prim", header.fn_helper_prim, fn_helpers)?;
        let non_defns = primitives
            .values()
            .filter(|e| e.role == PrimitiveRole::TypeOrCtor)
            .count();
        check_count("non_defn_prim", header.non_defn_prim, non_defns)?;
        let direct_prims = primitives
            .values()
            .filter(|e| matches!(e.role, PrimitiveRole::ParserDef | PrimitiveRole::Combinator))
            .count();
        check_count("direct_prim", header.direct_prim, direct_prims)?;

        let gen_parsers = generatables
            .values()
            .filter(|e| e.role == GeneratableRole::ParserDef)
            .count();
        check_count(
            "generatable_parsers",
            header.generatable_parsers,
            gen_parsers,
        )?;
        let gen_helpers = generatables
            .values()
            .filter(|e| e.role == GeneratableRole::Helper)
            .count();
        check_count(
            "generatable_helpers",
            header.generatable_helpers,
            gen_helpers,
        )?;
        check_count(
            "total_parsers",
            header.total_parsers,
            gen_parsers + prim_parsers,
        )?;

        // Verify closure totality for every Lean.Parser.* symbol referenced in any AST.
        let allowed_non_parsers: BTreeSet<Name> = KNOWN_NON_PARSER_LP_CONSTS
            .iter()
            .map(|s| parse_dotted_name(s))
            .collect();
        for entry in generatables.values() {
            let mut refs = Vec::new();
            collect_ast_const_refs(&entry.ast, &mut refs);
            for target in refs {
                let rendered = target.to_display_string();
                if rendered.starts_with("Lean.Parser.")
                    && !primitives.contains_key(&target)
                    && !generatables.contains_key(&target)
                    && !allowed_non_parsers.contains(&target)
                {
                    return Err(BuiltinTableError::UnresolvedParserRef {
                        owner: entry.name.to_display_string(),
                        target: rendered,
                    });
                }
            }
        }

        // Canonicalize category entry order (highest priority first, then name).
        for slot in categories.values_mut() {
            slot.leading.sort_by(|a, b| {
                b.priority
                    .cmp(&a.priority)
                    .then_with(|| a.decl.cmp(&b.decl))
            });
            slot.trailing.sort_by(|a, b| {
                b.priority
                    .cmp(&a.priority)
                    .then_with(|| a.decl.cmp(&b.decl))
            });
        }

        Ok(Self {
            header,
            primitives,
            generatables,
            categories,
        })
    }

    /// Collect every literal symbol token string referenced by `symbol`, `symbolNoAntiquot`,
    /// `nonReservedSymbol`, `nonReservedSymbolNoAntiquot`, `unicodeSymbol`, and `sepBy*`
    /// calls across all generatable builtin parsers.
    pub fn collect_literal_tokens(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        for entry in self.generatables.values() {
            collect_ast_tokens(&entry.ast, &mut out);
        }
        out
    }

    /// Runtime primitive count (primitives excluding pure type/constructor names).
    pub fn runtime_primitive_count(&self) -> usize {
        self.primitives
            .values()
            .filter(|e| e.role != PrimitiveRole::TypeOrCtor)
            .count()
    }
}

fn check_count(
    field: &'static str,
    declared: usize,
    found: usize,
) -> Result<(), BuiltinTableError> {
    if declared == found {
        Ok(())
    } else {
        Err(BuiltinTableError::CountMismatch {
            field,
            declared,
            found,
        })
    }
}

fn parse_dotted_name(raw: &str) -> Name {
    if raw.is_empty() || raw == "[anonymous]" {
        return Name::anonymous();
    }
    let mut acc = Name::anonymous();
    for part in raw.split('.') {
        if let Ok(num) = part.parse::<u64>() {
            acc = Name::num(acc, num);
        } else {
            acc = Name::str(acc, part);
        }
    }
    acc
}

fn collect_ast_const_refs(ast: &CombinatorAst, out: &mut Vec<Name>) {
    let mut stack = vec![ast];
    while let Some(node) = stack.pop() {
        match node {
            CombinatorAst::Const(n) => out.push(n.clone()),
            CombinatorAst::Call { func, args } => {
                out.push(func.clone());
                stack.extend(args.iter());
            }
            CombinatorAst::App { func, args } => {
                stack.push(func);
                stack.extend(args.iter());
            }
            CombinatorAst::Seq(a, b)
            | CombinatorAst::OrElse(a, b)
            | CombinatorAst::Append(a, b)
            | CombinatorAst::Beq(a, b)
            | CombinatorAst::BoolOr(a, b) => {
                stack.push(b);
                stack.push(a);
            }
            CombinatorAst::Lam { body, .. } | CombinatorAst::SomeVal(body) => stack.push(body),
            CombinatorAst::Let { val, body, .. } => {
                stack.push(body);
                stack.push(val);
            }
            CombinatorAst::Ite {
                cond,
                then_branch,
                else_branch,
            } => {
                stack.push(else_branch);
                stack.push(then_branch);
                stack.push(cond);
            }
            CombinatorAst::LitList(items) => stack.extend(items.iter()),
            CombinatorAst::NoneVal
            | CombinatorAst::Var { .. }
            | CombinatorAst::LitNat(_)
            | CombinatorAst::LitStr(_)
            | CombinatorAst::LitName(_)
            | CombinatorAst::LitBool(_)
            | CombinatorAst::LitChar(_) => {}
        }
    }
}

fn collect_ast_tokens(ast: &CombinatorAst, out: &mut BTreeSet<String>) {
    let mut stack = vec![ast];
    while let Some(node) = stack.pop() {
        match node {
            CombinatorAst::Call { func, args } => {
                let name = func.to_display_string();
                match name.as_str() {
                    "Lean.Parser.symbol"
                    | "Lean.Parser.symbolNoAntiquot"
                    | "Lean.Parser.nonReservedSymbol"
                    | "Lean.Parser.nonReservedSymbolNoAntiquot" => {
                        if let Some(CombinatorAst::LitStr(tok)) = args.first() {
                            let trimmed = tok.trim();
                            if !trimmed.is_empty() {
                                out.insert(trimmed.to_owned());
                            }
                        }
                    }
                    "Lean.Parser.unicodeSymbol" | "Lean.Parser.unicodeSymbolNoAntiquot" => {
                        for arg in args.iter().take(2) {
                            if let CombinatorAst::LitStr(tok) = arg {
                                let trimmed = tok.trim();
                                if !trimmed.is_empty() {
                                    out.insert(trimmed.to_owned());
                                }
                            }
                        }
                    }
                    "Lean.Parser.sepBy"
                    | "Lean.Parser.sepBy1"
                    | "Lean.Parser.sepByNoAntiquot"
                    | "Lean.Parser.sepBy1NoAntiquot" => {
                        if let Some(CombinatorAst::LitStr(tok)) = args.get(1) {
                            let trimmed = tok.trim();
                            if !trimmed.is_empty() {
                                out.insert(trimmed.to_owned());
                            }
                        }
                    }
                    _ => {}
                }
                stack.extend(args.iter());
            }
            CombinatorAst::App { func, args } => {
                stack.push(func);
                stack.extend(args.iter());
            }
            CombinatorAst::Seq(a, b)
            | CombinatorAst::OrElse(a, b)
            | CombinatorAst::Append(a, b)
            | CombinatorAst::Beq(a, b)
            | CombinatorAst::BoolOr(a, b) => {
                stack.push(b);
                stack.push(a);
            }
            CombinatorAst::Lam { body, .. } | CombinatorAst::SomeVal(body) => stack.push(body),
            CombinatorAst::Let { val, body, .. } => {
                stack.push(body);
                stack.push(val);
            }
            CombinatorAst::Ite {
                cond,
                then_branch,
                else_branch,
            } => {
                stack.push(else_branch);
                stack.push(then_branch);
                stack.push(cond);
            }
            CombinatorAst::LitList(items) => stack.extend(items.iter()),
            _ => {}
        }
    }
}

// ---- Minimal zero-dependency JSON reader (Doctrine D1) ----------------------

#[derive(Debug, Clone)]
enum JsonVal {
    Null,
    Bool(bool),
    Num(u64),
    Str(String),
    Arr(Vec<JsonVal>),
    Obj(BTreeMap<String, JsonVal>),
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
    depth: usize,
}

impl<'a> JsonParser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            bytes: input.as_bytes(),
            pos: 0,
            depth: 0,
        }
    }

    fn skip_ws(&mut self) {
        while let Some(&b) = self.bytes.get(self.pos) {
            if matches!(b, b' ' | b'\t' | b'\r' | b'\n') {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn parse_value(&mut self) -> Result<JsonVal, String> {
        self.skip_ws();
        let Some(&b) = self.bytes.get(self.pos) else {
            return Err("unexpected end of JSON".to_owned());
        };
        match b {
            b'{' => self.parse_object(),
            b'[' => self.parse_array(),
            b'"' => self.parse_string().map(JsonVal::Str),
            b't' => self.expect_bytes(b"true", JsonVal::Bool(true)),
            b'f' => self.expect_bytes(b"false", JsonVal::Bool(false)),
            b'n' => self.expect_bytes(b"null", JsonVal::Null),
            b'0'..=b'9' => self.parse_uint().map(JsonVal::Num),
            other => Err(format!(
                "unexpected byte 0x{other:02x} at offset {}",
                self.pos
            )),
        }
    }

    fn expect_bytes(&mut self, lit: &[u8], val: JsonVal) -> Result<JsonVal, String> {
        if self.bytes.get(self.pos..self.pos + lit.len()) == Some(lit) {
            self.pos += lit.len();
            Ok(val)
        } else {
            Err(format!("expected literal at offset {}", self.pos))
        }
    }

    fn parse_uint(&mut self) -> Result<u64, String> {
        let start = self.pos;
        while let Some(&b) = self.bytes.get(self.pos) {
            if b.is_ascii_digit() {
                self.pos += 1;
            } else {
                break;
            }
        }
        let slice = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| "invalid UTF-8 in integer".to_owned())?;
        slice
            .parse::<u64>()
            .map_err(|_| format!("integer overflow or malformed number {slice:?}"))
    }

    fn parse_string(&mut self) -> Result<String, String> {
        if self.bytes.get(self.pos) != Some(&b'"') {
            return Err(format!("expected '\"' at offset {}", self.pos));
        }
        self.pos += 1;
        let mut out = String::new();
        while let Some(&b) = self.bytes.get(self.pos) {
            if b == b'"' {
                self.pos += 1;
                return Ok(out);
            }
            if b == b'\\' {
                self.pos += 1;
                let Some(&esc) = self.bytes.get(self.pos) else {
                    return Err("unterminated escape sequence".to_owned());
                };
                self.pos += 1;
                match esc {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'b' => out.push('\u{0008}'),
                    b'f' => out.push('\u{000C}'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'u' => {
                        let code = self.parse_hex4()?;
                        let ch = if (0xD800..=0xDBFF).contains(&code) {
                            if self.bytes.get(self.pos..self.pos + 2) != Some(b"\\u") {
                                return Err("unpaired high surrogate".to_owned());
                            }
                            self.pos += 2;
                            let low = self.parse_hex4()?;
                            if !(0xDC00..=0xDFFF).contains(&low) {
                                return Err("invalid low surrogate".to_owned());
                            }
                            let combined =
                                0x10000 + (((code as u32 - 0xD800) << 10) | (low as u32 - 0xDC00));
                            char::from_u32(combined).ok_or("invalid surrogate scalar")?
                        } else {
                            char::from_u32(code as u32).ok_or("invalid \\u scalar")?
                        };
                        out.push(ch);
                    }
                    other => return Err(format!("unknown JSON escape \\x{other:02x}")),
                }
            } else if b < 0x80 {
                out.push(b as char);
                self.pos += 1;
            } else {
                let tail = std::str::from_utf8(&self.bytes[self.pos..])
                    .map_err(|_| "invalid UTF-8 in JSON string".to_owned())?;
                let ch = tail
                    .chars()
                    .next()
                    .ok_or_else(|| "unexpected EOF in UTF-8 string".to_owned())?;
                out.push(ch);
                self.pos += ch.len_utf8();
            }
        }
        Err("unterminated JSON string".to_owned())
    }

    fn parse_hex4(&mut self) -> Result<u16, String> {
        let Some(slice) = self.bytes.get(self.pos..self.pos + 4) else {
            return Err("truncated \\uXXXX escape".to_owned());
        };
        let s = std::str::from_utf8(slice).map_err(|_| "non-ASCII \\uXXXX escape".to_owned())?;
        self.pos += 4;
        u16::from_str_radix(s, 16).map_err(|_| format!("invalid hex escape \\u{s}"))
    }

    fn parse_array(&mut self) -> Result<JsonVal, String> {
        self.depth += 1;
        if self.depth > MAX_JSON_DEPTH {
            return Err("JSON nesting depth exceeded".to_owned());
        }
        self.pos += 1; // '['
        let mut items = Vec::new();
        self.skip_ws();
        if self.bytes.get(self.pos) == Some(&b']') {
            self.pos += 1;
            self.depth -= 1;
            return Ok(JsonVal::Arr(items));
        }
        loop {
            items.push(self.parse_value()?);
            self.skip_ws();
            match self.bytes.get(self.pos) {
                Some(&b',') => {
                    self.pos += 1;
                }
                Some(&b']') => {
                    self.pos += 1;
                    self.depth -= 1;
                    return Ok(JsonVal::Arr(items));
                }
                _ => return Err(format!("expected ',' or ']' at offset {}", self.pos)),
            }
        }
    }

    fn parse_object(&mut self) -> Result<JsonVal, String> {
        self.depth += 1;
        if self.depth > MAX_JSON_DEPTH {
            return Err("JSON nesting depth exceeded".to_owned());
        }
        self.pos += 1; // '{'
        let mut map = BTreeMap::new();
        self.skip_ws();
        if self.bytes.get(self.pos) == Some(&b'}') {
            self.pos += 1;
            self.depth -= 1;
            return Ok(JsonVal::Obj(map));
        }
        loop {
            self.skip_ws();
            let key = self.parse_string()?;
            self.skip_ws();
            if self.bytes.get(self.pos) != Some(&b':') {
                return Err(format!("expected ':' at offset {}", self.pos));
            }
            self.pos += 1;
            let val = self.parse_value()?;
            map.insert(key, val);
            self.skip_ws();
            match self.bytes.get(self.pos) {
                Some(&b',') => {
                    self.pos += 1;
                }
                Some(&b'}') => {
                    self.pos += 1;
                    self.depth -= 1;
                    return Ok(JsonVal::Obj(map));
                }
                _ => return Err(format!("expected ',' or '}}' at offset {}", self.pos)),
            }
        }
    }
}

fn parse_json(line: &str) -> Result<JsonVal, String> {
    let mut parser = JsonParser::new(line);
    let val = parser.parse_value()?;
    parser.skip_ws();
    if parser.pos != parser.bytes.len() {
        return Err(format!("trailing bytes at offset {}", parser.pos));
    }
    Ok(val)
}

fn as_obj<'a>(
    val: &'a JsonVal,
    line: usize,
    msg: &str,
) -> Result<&'a BTreeMap<String, JsonVal>, BuiltinTableError> {
    match val {
        JsonVal::Obj(map) => Ok(map),
        _ => Err(BuiltinTableError::MalformedRow {
            line,
            detail: msg.to_owned(),
        }),
    }
}

fn req_str<'a>(
    obj: &'a BTreeMap<String, JsonVal>,
    key: &str,
    line: usize,
) -> Result<&'a str, BuiltinTableError> {
    match obj.get(key) {
        Some(JsonVal::Str(s)) => Ok(s.as_str()),
        _ => Err(BuiltinTableError::MalformedRow {
            line,
            detail: format!("missing or non-string field {key:?}"),
        }),
    }
}

fn req_bool(
    obj: &BTreeMap<String, JsonVal>,
    key: &str,
    line: usize,
) -> Result<bool, BuiltinTableError> {
    match obj.get(key) {
        Some(JsonVal::Bool(b)) => Ok(*b),
        _ => Err(BuiltinTableError::MalformedRow {
            line,
            detail: format!("missing or non-bool field {key:?}"),
        }),
    }
}

fn req_u64(
    obj: &BTreeMap<String, JsonVal>,
    key: &str,
    line: usize,
) -> Result<u64, BuiltinTableError> {
    match obj.get(key) {
        Some(JsonVal::Num(n)) => Ok(*n),
        _ => Err(BuiltinTableError::MalformedRow {
            line,
            detail: format!("missing or non-integer field {key:?}"),
        }),
    }
}

fn req_usize(
    obj: &BTreeMap<String, JsonVal>,
    key: &str,
    line: usize,
) -> Result<usize, BuiltinTableError> {
    let n = req_u64(obj, key, line)?;
    usize::try_from(n).map_err(|_| BuiltinTableError::MalformedRow {
        line,
        detail: format!("field {key:?} out of usize range"),
    })
}

fn parse_string_array(
    obj: &BTreeMap<String, JsonVal>,
    key: &str,
    line: usize,
) -> Result<Vec<String>, BuiltinTableError> {
    let Some(JsonVal::Arr(arr)) = obj.get(key) else {
        return Err(BuiltinTableError::MalformedRow {
            line,
            detail: format!("missing or non-array field {key:?}"),
        });
    };
    let mut out = Vec::with_capacity(arr.len());
    for item in arr {
        match item {
            JsonVal::Str(s) => out.push(s.clone()),
            _ => {
                return Err(BuiltinTableError::MalformedRow {
                    line,
                    detail: format!("non-string element in array {key:?}"),
                });
            }
        }
    }
    Ok(out)
}

fn parse_name_array(
    obj: &BTreeMap<String, JsonVal>,
    key: &str,
    line: usize,
) -> Result<Vec<Name>, BuiltinTableError> {
    Ok(parse_string_array(obj, key, line)?
        .into_iter()
        .map(|s| parse_dotted_name(&s))
        .collect())
}

fn parse_registrations(
    obj: &BTreeMap<String, JsonVal>,
    line: usize,
) -> Result<Vec<BuiltinRegistration>, BuiltinTableError> {
    let Some(JsonVal::Arr(arr)) = obj.get("registrations") else {
        return Err(BuiltinTableError::MalformedRow {
            line,
            detail: "missing or non-array field 'registrations'".to_owned(),
        });
    };
    let mut out = Vec::with_capacity(arr.len());
    for item in arr {
        let robj = as_obj(item, line, "registration entry must be an object")?;
        let cat = parse_dotted_name(req_str(robj, "cat", line)?);
        let leading = req_bool(robj, "leading", line)?;
        let prio_u64 = req_u64(robj, "prio", line)?;
        let priority = u32::try_from(prio_u64).map_err(|_| BuiltinTableError::MalformedRow {
            line,
            detail: "registration priority exceeds u32".to_owned(),
        })?;
        out.push(BuiltinRegistration {
            category: cat,
            leading,
            priority,
        });
    }
    Ok(out)
}

fn parse_ast(val: &JsonVal, line: usize) -> Result<CombinatorAst, BuiltinTableError> {
    let obj = as_obj(val, line, "AST node must be an object")?;
    if let Some(JsonVal::Str(op)) = obj.get("op") {
        let req_child = |k: &str| -> Result<Box<CombinatorAst>, BuiltinTableError> {
            let child = obj.get(k).ok_or_else(|| BuiltinTableError::MalformedRow {
                line,
                detail: format!("op {op:?} missing field {k:?}"),
            })?;
            Ok(Box::new(parse_ast(child, line)?))
        };
        return match op.as_str() {
            "seq" => Ok(CombinatorAst::Seq(req_child("lhs")?, req_child("rhs")?)),
            "orelse" => Ok(CombinatorAst::OrElse(req_child("lhs")?, req_child("rhs")?)),
            "append" => Ok(CombinatorAst::Append(req_child("lhs")?, req_child("rhs")?)),
            "beq" => Ok(CombinatorAst::Beq(req_child("lhs")?, req_child("rhs")?)),
            "bool_or" => Ok(CombinatorAst::BoolOr(req_child("lhs")?, req_child("rhs")?)),
            "none" => Ok(CombinatorAst::NoneVal),
            "some" => Ok(CombinatorAst::SomeVal(req_child("value")?)),
            "lam" => Ok(CombinatorAst::Lam {
                param: req_str(obj, "param", line)?.to_owned(),
                body: req_child("body")?,
            }),
            "let" => Ok(CombinatorAst::Let {
                name: req_str(obj, "name", line)?.to_owned(),
                val: req_child("val")?,
                body: req_child("body")?,
            }),
            "ite" => Ok(CombinatorAst::Ite {
                cond: req_child("cond")?,
                then_branch: req_child("then")?,
                else_branch: req_child("else")?,
            }),
            "call" => {
                let func = parse_dotted_name(req_str(obj, "fn", line)?);
                let Some(JsonVal::Arr(raw_args)) = obj.get("args") else {
                    return Err(BuiltinTableError::MalformedRow {
                        line,
                        detail: "call op missing 'args' array".to_owned(),
                    });
                };
                let mut args = Vec::with_capacity(raw_args.len());
                for a in raw_args {
                    args.push(parse_ast(a, line)?);
                }
                Ok(CombinatorAst::Call { func, args })
            }
            "app" => {
                let func = req_child("fn")?;
                let Some(JsonVal::Arr(raw_args)) = obj.get("args") else {
                    return Err(BuiltinTableError::MalformedRow {
                        line,
                        detail: "app op missing 'args' array".to_owned(),
                    });
                };
                let mut args = Vec::with_capacity(raw_args.len());
                for a in raw_args {
                    args.push(parse_ast(a, line)?);
                }
                Ok(CombinatorAst::App { func, args })
            }
            other => Err(BuiltinTableError::MalformedRow {
                line,
                detail: format!("unknown AST op {other:?}"),
            }),
        };
    }
    if let Some(JsonVal::Str(lit)) = obj.get("lit") {
        return match lit.as_str() {
            "nat" => Ok(CombinatorAst::LitNat(req_u64(obj, "value", line)?)),
            "str" => Ok(CombinatorAst::LitStr(
                req_str(obj, "value", line)?.to_owned(),
            )),
            "name" => Ok(CombinatorAst::LitName(parse_dotted_name(req_str(
                obj, "value", line,
            )?))),
            "bool" => Ok(CombinatorAst::LitBool(req_bool(obj, "value", line)?)),
            "char" => {
                let code_u64 = req_u64(obj, "code", line)?;
                let code =
                    u32::try_from(code_u64).map_err(|_| BuiltinTableError::MalformedRow {
                        line,
                        detail: "char literal code exceeds u32".to_owned(),
                    })?;
                Ok(CombinatorAst::LitChar(code))
            }
            "list" => {
                let Some(JsonVal::Arr(raw_items)) = obj.get("items") else {
                    return Err(BuiltinTableError::MalformedRow {
                        line,
                        detail: "list literal missing 'items' array".to_owned(),
                    });
                };
                let mut items = Vec::with_capacity(raw_items.len());
                for item in raw_items {
                    items.push(parse_ast(item, line)?);
                }
                Ok(CombinatorAst::LitList(items))
            }
            other => Err(BuiltinTableError::MalformedRow {
                line,
                detail: format!("unknown AST literal {other:?}"),
            }),
        };
    }
    if let Some(JsonVal::Str(c)) = obj.get("const") {
        return Ok(CombinatorAst::Const(parse_dotted_name(c)));
    }
    if let Some(JsonVal::Str(v)) = obj.get("var") {
        return Ok(CombinatorAst::Var {
            name: v.clone(),
            idx: req_usize(obj, "idx", line)?,
        });
    }
    Err(BuiltinTableError::MalformedRow {
        line,
        detail: format!(
            "unrecognized AST node keys: {:?}",
            obj.keys().collect::<Vec<_>>()
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_builtin_parser_table_validates_and_matches_pinned_floor() {
        let table = reference_builtin_parser_table();
        assert_eq!(table.header.lean_version, "4.32.0");
        assert_eq!(
            table.header.githash,
            "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
        );
        assert_eq!(table.header.total_parsers, 497);
        assert_eq!(table.header.generatable_parsers, 480);
        assert_eq!(table.header.primitive_parsers, 17);
        assert_eq!(table.header.generatable_helpers, 61);
        assert_eq!(table.header.primitive_total, 64);
        assert_eq!(table.runtime_primitive_count(), 60);
        assert_eq!(table.primitives.len(), 64);
        assert_eq!(table.generatables.len(), 541);

        // Verify all 10 builtin categories and 239 registrations are indexed.
        assert_eq!(table.categories.len(), 10);
        let total_regs: usize = table
            .categories
            .values()
            .map(|c| c.leading.len() + c.trailing.len())
            .sum();
        assert_eq!(total_regs, 239);

        // Spot-check Lean.Parser.Term.app AST structure.
        let app_entry = table
            .generatables
            .get(&parse_dotted_name("Lean.Parser.Term.app"))
            .expect("Lean.Parser.Term.app present");
        assert!(app_entry.is_trailing);
        assert_eq!(app_entry.role, GeneratableRole::ParserDef);
        assert!(matches!(
            &app_entry.ast,
            CombinatorAst::Call { func, args }
                if func.to_display_string() == "Lean.Parser.trailingNode" && args.len() == 4
        ));

        // Verify static literal token collection finds core keywords.
        let tokens = table.collect_literal_tokens();
        assert!(
            tokens.len() >= 150,
            "expected >= 150 literal tokens, got {}",
            tokens.len()
        );
        for kw in [
            "def",
            "theorem",
            "inductive",
            "structure",
            "match",
            "fun",
            "by",
            "where",
        ] {
            assert!(tokens.contains(kw), "missing expected builtin token {kw:?}");
        }
    }

    #[test]
    fn malformed_tables_and_mutants_are_refused() {
        assert_eq!(BuiltinParserTable::parse(""), Err(BuiltinTableError::Empty));

        let bad_schema = BUILTIN_PARSER_TABLE.replacen(
            "fln.builtin-parser-table/1",
            "fln.builtin-parser-table/99",
            1,
        );
        assert!(matches!(
            BuiltinParserTable::parse(&bad_schema),
            Err(BuiltinTableError::Schema { .. })
        ));

        // Truncate last row -> header count mismatch must fire.
        let truncated: String = BUILTIN_PARSER_TABLE
            .lines()
            .take(BUILTIN_PARSER_TABLE.lines().count() - 1)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(matches!(
            BuiltinParserTable::parse(&truncated),
            Err(BuiltinTableError::CountMismatch { .. })
        ));

        // Plant an unclassified Lean.Parser.* constant reference -> totality check must refuse.
        let bad_ref = BUILTIN_PARSER_TABLE.replacen(
            "\"const\":\"Lean.Parser.Term.argument\"",
            "\"const\":\"Lean.Parser.PhantomUnclassified\"",
            1,
        );
        assert!(matches!(
            BuiltinParserTable::parse(&bad_ref),
            Err(BuiltinTableError::UnresolvedParserRef { ref target, .. })
                if target == "Lean.Parser.PhantomUnclassified"
        ));
    }
}
