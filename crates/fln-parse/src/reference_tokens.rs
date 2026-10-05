//! The production lexer's token table, derived from the pin and never transcribed (Rule D5;
//! beads `fln-vokf`, `fln-notation-from-imports-0edr`).
//!
//! ## Where Lean's tokens come from
//!
//! Upstream has no fixed token list (see `fln_syntax::token`). A file's table is the union of
//! two sources, both recorded in `contracts/REFERENCE_GRAMMAR_CENSUS.txt` by
//! `scripts/extract/gen_grammar_census.sh` from the pinned Reference:
//!
//! 1. **The builtin table.** Every builtin parser compiled into the binary registers the tokens
//!    its `ParserInfo` collects (`addBuiltinParser` → `updateBuiltinTokens`). Every environment
//!    starts from this table whatever it imports, so `⟨`, `fun`, `by` and `match` are tokens even
//!    in a `prelude` file that imports nothing. Census rows `builtin-token`.
//! 2. **Imported syntax.** `syntax`, `notation`, `infixl`, … record parser-extension `token`
//!    entries in the module that declares them, and a file sees the entries of its whole import
//!    closure. `+`, `=` and `≤` arrive this way, from `Init`. Census rows `module` (imports) and
//!    `module-tokens` (the module's own entries).
//!
//! The module header is parsed before any import is loaded, against the builtin table plus the
//! header parser's own tokens (`Lean.Parser.Module.updateTokens`): census rows `header-token`.
//!
//! The closure rule — builtin table plus the global token entries of the reflexive-transitive
//! import closure — is not assumed: the extractor compares it with the table `importModules`
//! actually builds for six sample closures and refuses to publish on any difference (census rows
//! `closure-check`, whose sizes [`TokenCensus::table_for`] reproduces in this crate's tests).
//!
//! ## What production uses, and what it does not yet do
//!
//! The source pipeline lexes a body without being told the file's imports, so production lexes
//! every body with the table of an ordinary file: no `prelude`, hence exactly the implicit
//! `import Init` ([`implicit_init_table`]). That is the Reference's table for every file that
//! imports nothing beyond `Init`. It is NOT the Reference's table for:
//!
//! * a `prelude` file, which sees only its explicit closure (`prelude import Init.Prelude` sees the
//!   238 builtin tokens and not `+`, `=` or `at`);
//! * a file importing a module outside the census (Lean.*, Mathlib, user modules), whose tokens
//!   this census cannot know — decoding them from the imported `.olean` journals is the remaining
//!   half of `fln-notation-from-imports-0edr`;
//! * `scoped` syntax, whose tokens are active only after `open` (the census omits them).
//!
//! [`TokenCensus::table_for`] computes the faithful table for any header whose closure the
//! census covers, and refuses one it does not; threading it into the body parsers is the step
//! that retires the first gap.
//!
//! ## The declared remainder: keywords still lexed as identifiers
//!
//! Declaration bodies are lexed against [`production_table`], which is
//! [`implicit_init_table`] minus [`SEED_IDENTIFIER_ALLOWANCE`]. Every other keyword at the pin is
//! reserved, as in the Reference (bead `franken_lean-z8j.1.6.2`). Every allowed word is a known
//! Reference divergence: FrankenLean accepts programs that use it as a name, and the pinned
//! Reference rejects them. See the constant for why it exists and how it shrinks.

use fln_core::name::Name;
use fln_syntax::token::TokenTable;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::OnceLock;

/// The checked-in census, as generated from the pin.
pub const GRAMMAR_CENSUS: &str = include_str!("../../../contracts/REFERENCE_GRAMMAR_CENSUS.txt");

const SCHEMA: &str = "fln-reference-grammar-census/1";

/// One source that still uses an allowed keyword as a name: a repository-relative file and
/// the exact text in it that does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllowanceWitness {
    pub file: &'static str,
    pub snippet: &'static str,
}

const fn witness(file: &'static str, snippet: &'static str) -> AllowanceWitness {
    AllowanceWitness { file, snippet }
}

/// A declared one-way allowance preserving frozen seed-dialect behavior. It is NOT Lean
/// compatibility.
///
/// Every word here is a keyword at the pin, and every one is a known Reference divergence:
/// FrankenLean accepts programs that use it as a name, which the pinned Reference rejects
/// (`expected identifier`). The words are lexed as identifiers only so that the frozen
/// seed-dialect examples and the existing tests listed with each word keep their present
/// verdicts until their owners rename the names (the examples' ledger rows are `fln-defect`).
/// This is global lexer behavior: no declaration body reserves these words, whichever file is
/// being lexed, because the lexer cannot tell a seed-dialect file from a Lean file. The
/// witnesses are a documentation and ratchet binding only. `tests/reference_grammar_census.rs`
/// pins the set by equality and requires every witness to still occur, so when a listed use is
/// renamed its witness must go, and when a word's last witness goes the word must go: the set
/// only shrinks.
pub const SEED_IDENTIFIER_ALLOWANCE: &[(&str, &[AllowanceWitness])] = &[
    (
        "end",
        &[witness(
            "examples/native_index_refinement.lean",
            "| cons j y end =>",
        )],
    ),
    (
        "exists",
        &[
            witness(
                "crates/fln/tests/source_construction.rs",
                "theorem exists : Witness (fun n => n = 7)",
            ),
            witness(
                "crates/fln/tests/source_refinement.rs",
                "theorem exists : Witness (fun n => n = 7)",
            ),
        ],
    ),
    (
        "from",
        &[witness(
            "crates/fln/tests/source_recursion.rs",
            "def weight {A : Type} (from to : A)",
        )],
    ),
    (
        "local",
        &[witness(
            "examples/native_tactic_repetition.lean",
            "theorem local (n : Nat)",
        )],
    ),
    (
        "opaque",
        &[witness(
            "crates/fln-elab/tests/source_term_assertions.rs",
            "theorem opaque : 0 = 0",
        )],
    ),
    (
        "open",
        &[witness(
            "crates/fln-cli/src/lib.rs",
            "def open (value : String) : String := value",
        )],
    ),
    (
        "partial",
        &[
            witness(
                "crates/fln/tests/runtime_mutual_recursion.rs",
                "def partial (t : Tree)",
            ),
            witness(
                "crates/fln/tests/source_named_arguments.rs",
                "theorem partial : (three 1)",
            ),
        ],
    ),
    (
        "postfix",
        &[witness(
            "crates/fln/tests/source_record_literals.rs",
            "theorem postfix : (factory).value = 0",
        )],
    ),
    (
        "prefix",
        &[witness(
            "examples/native_closure_data.lean",
            "(prefix : String)",
        )],
    ),
    (
        "repeat",
        &[witness(
            "examples/native_recursion.lean",
            "def repeat (n : Nat)",
        )],
    ),
    (
        "scoped",
        &[witness(
            "examples/native_decidable_cases.lean",
            "theorem scoped (p q : Prop)",
        )],
    ),
    (
        "universe",
        &[witness(
            "examples/native_default_simp.lean",
            "theorem universe (A : Type)",
        )],
    ),
];

/// A floor on the builtin table. The pin has 238; a census that parses but yields far fewer was
/// truncated or mis-generated, and an empty table would make every symbol a lexical refusal.
const MIN_BUILTIN_TOKENS: usize = 200;

/// Why the census text cannot be used.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CensusError {
    /// The first data row is not this crate's schema.
    Schema { found: Option<String> },
    /// A row this module consumes does not have its shape.
    Malformed { line: usize, reason: &'static str },
    /// A token or module appears twice where the extractor emits it once.
    Duplicate { line: usize, what: String },
    /// A `count` row disagrees with the rows present: a truncated or hand-edited census.
    CountMismatch {
        what: &'static str,
        declared: usize,
        found: usize,
    },
    /// The builtin table is implausibly small.
    TooFewBuiltinTokens { found: usize },
    /// A census module imports a module the census does not describe, so closures are not
    /// computable from it.
    OpenClosure { module: String, import: String },
}

impl fmt::Display for CensusError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Schema { found } => write!(f, "expected schema {SCHEMA}, found {found:?}"),
            Self::Malformed { line, reason } => write!(f, "line {line}: {reason}"),
            Self::Duplicate { line, what } => write!(f, "line {line}: duplicate {what}"),
            Self::CountMismatch {
                what,
                declared,
                found,
            } => write!(f, "count {what} declares {declared}, rows give {found}"),
            Self::TooFewBuiltinTokens { found } => write!(
                f,
                "{found} builtin tokens is below the floor of {MIN_BUILTIN_TOKENS}"
            ),
            Self::OpenClosure { module, import } => {
                write!(
                    f,
                    "module {module} imports {import}, which the census lacks"
                )
            }
        }
    }
}

/// A header names a module the census does not describe, so its token table is not derivable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownModule(pub Name);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct CensusModule {
    imports: Vec<Name>,
    global_tokens: BTreeSet<String>,
}

/// The token half of the grammar census.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenCensus {
    builtin: BTreeSet<String>,
    header_only: BTreeSet<String>,
    modules: BTreeMap<Name, CensusModule>,
}

fn module_name(text: &str) -> Option<Name> {
    // Init/Std module names need no escaping; one that would is refused rather than guessed.
    if text.is_empty() || text.contains(['«', '»']) || text.split('.').any(str::is_empty) {
        return None;
    }
    Some(Name::from_components(text.split('.')))
}

fn declared(
    counts: &BTreeMap<String, usize>,
    what: &'static str,
    found: usize,
) -> Result<(), CensusError> {
    match counts.get(what) {
        Some(&n) if n == found => Ok(()),
        Some(&n) => Err(CensusError::CountMismatch {
            what,
            declared: n,
            found,
        }),
        None => Err(CensusError::CountMismatch {
            what,
            declared: 0,
            found,
        }),
    }
}

impl TokenCensus {
    /// Parse the rows this crate consumes. Rows for other consumers are skipped; every consumed
    /// row is checked for shape, duplicates and its declared count, so a truncated census is a
    /// refusal and never a smaller table.
    pub fn parse(text: &str) -> Result<TokenCensus, CensusError> {
        let mut schema_seen = false;
        let mut counts = BTreeMap::new();
        let mut builtin = BTreeSet::new();
        let mut header_only = BTreeSet::new();
        let mut modules: BTreeMap<Name, CensusModule> = BTreeMap::new();
        let mut module_rows: BTreeSet<Name> = BTreeSet::new();
        for (index, row) in text.lines().enumerate() {
            let line = index + 1;
            if row.is_empty() || row.starts_with('#') {
                continue;
            }
            let fields: Vec<&str> = row.split('\t').collect();
            if !schema_seen {
                if fields.as_slice() != ["schema", SCHEMA] {
                    return Err(CensusError::Schema {
                        found: Some(row.to_string()),
                    });
                }
                schema_seen = true;
                continue;
            }
            let malformed = |reason| CensusError::Malformed { line, reason };
            match fields[0] {
                "count" => {
                    let [_, what, n] = fields.as_slice() else {
                        return Err(malformed("a count row has three fields"));
                    };
                    let n = n.parse().map_err(|_| malformed("a count is a numeral"))?;
                    counts.insert((*what).to_string(), n);
                }
                "builtin-token" => {
                    let [_, token, introducers] = fields.as_slice() else {
                        return Err(malformed("a builtin-token row has three fields"));
                    };
                    if !introducers.starts_with("introducers=") || !is_token(token) {
                        return Err(malformed(
                            "a builtin-token row names a token and its introducers",
                        ));
                    }
                    if !builtin.insert((*token).to_string()) {
                        return Err(CensusError::Duplicate {
                            line,
                            what: format!("builtin token {token}"),
                        });
                    }
                }
                "header-token" => {
                    let [_, token] = fields.as_slice() else {
                        return Err(malformed("a header-token row has two fields"));
                    };
                    if !is_token(token) {
                        return Err(malformed("a header token is a non-empty token"));
                    }
                    if !header_only.insert((*token).to_string()) {
                        return Err(CensusError::Duplicate {
                            line,
                            what: format!("header token {token}"),
                        });
                    }
                }
                "module" => {
                    let [_, module, imports] = fields.as_slice() else {
                        return Err(malformed("a module row has three fields"));
                    };
                    let module = module_name(module).ok_or_else(|| malformed("module name"))?;
                    let imports = imports
                        .strip_prefix("imports=")
                        .ok_or_else(|| malformed("a module row lists imports="))?;
                    let imports = imports
                        .split(' ')
                        .filter(|name| !name.is_empty())
                        .map(|name| module_name(name).ok_or_else(|| malformed("import name")))
                        .collect::<Result<Vec<_>, _>>()?;
                    if !module_rows.insert(module.clone()) {
                        return Err(CensusError::Duplicate {
                            line,
                            what: format!("module {}", module.to_display_string()),
                        });
                    }
                    modules.entry(module).or_default().imports = imports;
                }
                "module-tokens" => {
                    let [_, module, scope, tokens] = fields.as_slice() else {
                        return Err(malformed("a module-tokens row has four fields"));
                    };
                    let module = module_name(module).ok_or_else(|| malformed("module name"))?;
                    if *scope == "global" {
                        let entry = modules.entry(module).or_default();
                        if !entry.global_tokens.is_empty() {
                            return Err(CensusError::Duplicate {
                                line,
                                what: "global module-tokens row".to_string(),
                            });
                        }
                        for token in tokens.split(' ') {
                            if !is_token(token) {
                                return Err(malformed("a module token is a non-empty token"));
                            }
                            entry.global_tokens.insert(token.to_string());
                        }
                    } else if !scope.starts_with("scoped:") {
                        return Err(malformed("a module-tokens scope is global or scoped:<ns>"));
                    }
                    // Scoped tokens are active only after `open`; no production table uses them.
                }
                _ => {}
            }
        }
        if !schema_seen {
            return Err(CensusError::Schema { found: None });
        }
        declared(&counts, "builtin-tokens", builtin.len())?;
        declared(&counts, "header-only-tokens", header_only.len())?;
        declared(&counts, "init-std-modules", module_rows.len())?;
        if let Some(orphan) = modules.keys().find(|module| !module_rows.contains(*module)) {
            // a module-tokens row for a module that has no module row, hence no imports
            return Err(CensusError::OpenClosure {
                module: orphan.to_display_string(),
                import: "<no module row>".to_string(),
            });
        }
        if builtin.len() < MIN_BUILTIN_TOKENS {
            return Err(CensusError::TooFewBuiltinTokens {
                found: builtin.len(),
            });
        }
        for (module, entry) in &modules {
            for import in &entry.imports {
                if !modules.contains_key(import) {
                    return Err(CensusError::OpenClosure {
                        module: module.to_display_string(),
                        import: import.to_display_string(),
                    });
                }
            }
        }
        Ok(TokenCensus {
            builtin,
            header_only,
            modules,
        })
    }

    /// The builtin table: the tokens of every builtin parser in the pinned binary.
    pub fn builtin_tokens(&self) -> impl Iterator<Item = &str> {
        self.builtin.iter().map(String::as_str)
    }

    /// The tokens the module header parser adds for the header only (`prelude`, `module`, …).
    pub fn header_only_tokens(&self) -> impl Iterator<Item = &str> {
        self.header_only.iter().map(String::as_str)
    }

    /// Whether the census describes `module`.
    pub fn knows_module(&self, module: &Name) -> bool {
        self.modules.contains_key(module)
    }

    /// Every token a file with this header sees: the builtin table plus the global token entries
    /// of the reflexive-transitive closure of its imports, where a file without `prelude` also
    /// imports `Init`. A module the census does not describe is refused, never skipped: its
    /// tokens are unknown, and a table missing them would silently relex the file.
    pub fn tokens_for(
        &self,
        prelude: bool,
        imports: &[Name],
    ) -> Result<BTreeSet<String>, UnknownModule> {
        let mut roots: Vec<Name> = imports.to_vec();
        if !prelude {
            roots.push(Name::from_components(["Init"]));
        }
        let mut seen = BTreeSet::new();
        let mut tokens = self.builtin.clone();
        while let Some(module) = roots.pop() {
            if !seen.insert(module.clone()) {
                continue;
            }
            let Some(entry) = self.modules.get(&module) else {
                return Err(UnknownModule(module));
            };
            tokens.extend(entry.global_tokens.iter().cloned());
            roots.extend(entry.imports.iter().cloned());
        }
        Ok(tokens)
    }

    /// [`Self::tokens_for`] as a lexer table.
    pub fn table_for(&self, prelude: bool, imports: &[Name]) -> Result<TokenTable, UnknownModule> {
        self.tokens_for(prelude, imports)
            .map(TokenTable::from_tokens)
    }

    /// The table the module-header parser lexes against.
    pub fn header_table(&self) -> TokenTable {
        TokenTable::from_tokens(self.builtin.iter().chain(&self.header_only))
    }
}

fn is_token(token: &str) -> bool {
    !token.is_empty() && !token.chars().any(|c| c.is_whitespace() || c.is_control())
}

/// The checked-in census, parsed once. It is a compile-time constant, so a parse failure is a
/// build defect (held by this module's tests), never a property of user input.
pub fn reference_census() -> &'static TokenCensus {
    static CENSUS: OnceLock<TokenCensus> = OnceLock::new();
    CENSUS.get_or_init(|| match TokenCensus::parse(GRAMMAR_CENSUS) {
        Ok(census) => census,
        Err(error) => {
            panic!("invariant: contracts/REFERENCE_GRAMMAR_CENSUS.txt is unusable: {error}")
        }
    })
}

fn implicit_init_tokens() -> BTreeSet<String> {
    match reference_census().tokens_for(false, &[]) {
        Ok(tokens) => tokens,
        Err(UnknownModule(module)) => panic!(
            "invariant: the grammar census lacks the implicit import {}",
            module.to_display_string()
        ),
    }
}

/// The table of an ordinary file — no `prelude`, so exactly the implicit `import Init`. The
/// scope-command layer lexes against it. See the module docs for what this is not.
pub fn implicit_init_table() -> &'static TokenTable {
    static TABLE: OnceLock<TokenTable> = OnceLock::new();
    TABLE.get_or_init(|| TokenTable::from_tokens(implicit_init_tokens()))
}

/// The table declaration bodies are lexed against: [`implicit_init_table`] minus the declared
/// [`SEED_IDENTIFIER_ALLOWANCE`].
pub fn production_table() -> &'static TokenTable {
    static TABLE: OnceLock<TokenTable> = OnceLock::new();
    TABLE.get_or_init(|| {
        let mut tokens = implicit_init_tokens();
        for (word, _) in SEED_IDENTIFIER_ALLOWANCE {
            tokens.remove(*word);
        }
        TokenTable::from_tokens(tokens)
    })
}

/// The module-header table: builtin tokens plus the header parser's own.
pub fn header_table() -> &'static TokenTable {
    static TABLE: OnceLock<TokenTable> = OnceLock::new();
    TABLE.get_or_init(|| reference_census().header_table())
}
