//! Execute registered parser aliases in the live source grammar. The builtin
//! combinators and the file's ParserDescr entries share one Pratt interpreter.
//! This follows Parser.Extension.compileParserDescr; descriptions are compiled
//! only from the caller's active scope, never from the full import census.

use super::*;
use crate::extensions::{Descr, IdentBehavior, SyntaxDecl};

/// A sticky resource stop, independent of ordinary parser backtracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParserResourceLimit {
    Steps,
    Depth,
}

/// Why execution of a registered parser alias could not produce source syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserFailure {
    Description(CompileError),
    Syntax {
        unexpected: String,
        expected: Vec<String>,
    },
    Recovered {
        unexpected: String,
        expected: Vec<String>,
    },
    Resource(ParserResourceLimit),
    Boundary,
}

impl fmt::Display for ParserFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Description(error) => write!(f, "{error}"),
            Self::Syntax {
                unexpected,
                expected,
            }
            | Self::Recovered {
                unexpected,
                expected,
            } => {
                write!(f, "{unexpected}")?;
                if !expected.is_empty() {
                    write!(f, "; expected {}", expected.join(" or "))?;
                }
                Ok(())
            }
            Self::Resource(limit) => write!(f, "generated parser {limit:?} limit exhausted"),
            Self::Boundary => write!(f, "generated parser crossed its source operand boundary"),
        }
    }
}

pub(crate) struct ParserInput<'a> {
    pub source: &'a SourceText,
    pub start: usize,
    pub saved_pos: Option<usize>,
    pub quot_depth: u32,
    pub precedence: u32,
    pub max_steps: usize,
}

pub(crate) struct ParserRun {
    pub result: Result<Vec<Syntax>, (usize, ParserFailure)>,
    pub next: usize,
    pub steps: usize,
}

fn call(name: &str, args: Vec<CombinatorAst>) -> CombinatorAst {
    CombinatorAst::Call {
        func: Name::from_components(name.split('.')),
        args,
    }
}

/// Resolve only the registered alias names supplied by the checked-in census.
/// A declaration's name in the builtin table is not source visibility evidence.
fn alias_ast(
    alias: &Name,
    mut args: Vec<CombinatorAst>,
    aliases: &BTreeMap<String, Name>,
) -> Result<CombinatorAst, CompileError> {
    let name = alias.to_display_string();
    let decl = aliases
        .get(&name)
        .ok_or_else(|| CompileError::UnresolvedDecl(name.clone()))?;
    match (name.as_str(), args.as_slice()) {
        ("bracketedBinder", []) => args.push(CombinatorAst::LitBool(false)),
        ("patternIgnore", [body]) => {
            return Ok(call(
                "Lean.Parser.node",
                vec![
                    CombinatorAst::LitName(Name::from_components(["patternIgnore"])),
                    body.clone(),
                ],
            ));
        }
        ("andthen", [left, right]) => {
            return Ok(CombinatorAst::Seq(
                Box::new(left.clone()),
                Box::new(right.clone()),
            ));
        }
        ("orelse", [left, right]) => {
            return Ok(CombinatorAst::OrElse(
                Box::new(left.clone()),
                Box::new(right.clone()),
            ));
        }
        ("colEq" | "colGe" | "colGt" | "lineEq" | "ws" | "noWs" | "linebreak", []) => {
            // The aliases in Lean/Parser.lean instantiate the default message.
            let message = match name.as_str() {
                "ws" => "space before",
                "noWs" => "no space before",
                "linebreak" => "line break",
                "colEq" => "checkColEq",
                "colGe" => "checkColGe",
                "colGt" => "checkColGt",
                _ => "checkLineEq",
            };
            args.push(CombinatorAst::LitStr(message.to_owned()));
        }
        ("notFollowedBy", [_]) => args.push(CombinatorAst::LitStr("element".to_owned())),
        _ => {}
    }
    if args.is_empty() {
        Ok(CombinatorAst::Const(decl.clone()))
    } else {
        Ok(CombinatorAst::Call {
            func: decl.clone(),
            args,
        })
    }
}

fn descr_ast(
    descr: &Descr,
    aliases: &BTreeMap<String, Name>,
    depth: usize,
) -> Result<CombinatorAst, CompileError> {
    if depth > 64 {
        return Err(CompileError::DepthExceeded("active ParserDescr".to_owned()));
    }
    let child = |d| descr_ast(d, aliases, depth + 1);
    let name = |n: &Name| CombinatorAst::LitName(n.clone());
    let nat = |n: u32| CombinatorAst::LitNat(u64::from(n));
    let text = |s: &String| CombinatorAst::LitStr(s.clone());
    Ok(match descr {
        Descr::Const(n) => alias_ast(n, Vec::new(), aliases)?,
        Descr::Unary(n, p) => alias_ast(n, vec![child(p)?], aliases)?,
        Descr::Binary(n, p, q) => alias_ast(n, vec![child(p)?, child(q)?], aliases)?,
        Descr::Node { kind, prec, body } => call(
            "Lean.Parser.leadingNode",
            vec![name(kind), nat(*prec), child(body)?],
        ),
        Descr::TrailingNode {
            kind,
            prec,
            lhs_prec,
            body,
        } => call(
            "Lean.Parser.trailingNode",
            vec![name(kind), nat(*prec), nat(*lhs_prec), child(body)?],
        ),
        Descr::NodeWithAntiquot(label, kind, body) => call(
            "Lean.Parser.withCache",
            vec![
                name(kind),
                call(
                    "Lean.Parser.withAntiquot",
                    vec![
                        call(
                            "Lean.Parser.mkAntiquot",
                            vec![
                                text(label),
                                name(kind),
                                CombinatorAst::LitBool(true),
                                CombinatorAst::LitBool(false),
                            ],
                        ),
                        call("Lean.Parser.node", vec![name(kind), child(body)?]),
                    ],
                ),
            ],
        ),
        Descr::Symbol(s) => call("Lean.Parser.symbol", vec![text(s)]),
        Descr::NonReservedSymbol(s, include) => call(
            "Lean.Parser.nonReservedSymbol",
            vec![text(s), CombinatorAst::LitBool(*include)],
        ),
        Descr::UnicodeSymbol(s, ascii, preserve) => call(
            "Lean.Parser.unicodeSymbol",
            vec![text(s), text(ascii), CombinatorAst::LitBool(*preserve)],
        ),
        Descr::Cat(cat, prec) => call("Lean.Parser.categoryParser", vec![name(cat), nat(*prec)]),
        Descr::Parser(n) => CombinatorAst::Const(n.clone()),
        Descr::SepBy {
            item,
            separator,
            parser,
            trailing,
            at_least_one,
        } => call(
            if *at_least_one {
                "Lean.Parser.sepBy1"
            } else {
                "Lean.Parser.sepBy"
            },
            vec![
                child(item)?,
                text(separator),
                child(parser)?,
                CombinatorAst::LitBool(*trailing),
            ],
        ),
    })
}

/// Set of `'static` census `SyntaxDecl` pointers so only invariant census
/// descriptors are cached across files and scopes.
fn census_decl_ptrs() -> &'static HashSet<usize> {
    static PTRS: OnceLock<HashSet<usize>> = OnceLock::new();
    PTRS.get_or_init(|| {
        crate::extensions::extension_census()
            .decls()
            .iter()
            .map(|decl| Arc::as_ptr(decl) as usize)
            .collect()
    })
}

/// Lazy per-declaration cache of compiled `(ParserOp, FirstTokens)` for
/// `'static` census `SyntaxDecl`s, keyed by `Arc::as_ptr`. Compiling lazily on
/// demand avoids touching unused census entries on small `own_syntax_only()`
/// grammars while still eliminating redundant recompilation across files/scopes.
fn census_compiled_cache() -> &'static std::sync::Mutex<HashMap<usize, CompiledParser>> {
    static CACHE: OnceLock<std::sync::Mutex<HashMap<usize, CompiledParser>>> = OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(HashMap::new()))
}

impl BuiltinInterpreter {
    pub(super) fn compile_descr_op(
        &self,
        description: &Descr,
        aliases: &BTreeMap<String, Name>,
    ) -> Result<Arc<ParserOp>, CompileError> {
        let owner = Name::from_components(["active", "descriptor"]);
        let ast = descr_ast(description, aliases, 0)?;
        let value = eval_ast(
            reference_builtin_parser_table(),
            &self.def_index,
            &owner,
            &ast,
            &mut Vec::new(),
            0,
        )?;
        expect_parser(&owner, value)
    }

    pub(super) fn compile_alias_op(
        &self,
        alias: &Name,
        aliases: &BTreeMap<String, Name>,
    ) -> Result<Arc<ParserOp>, CompileError> {
        let ast = alias_ast(alias, Vec::new(), aliases)?;
        let value = eval_ast(
            reference_builtin_parser_table(),
            &self.def_index,
            alias,
            &ast,
            &mut Vec::new(),
            0,
        )?;
        expect_parser(alias, value)
    }

    pub(crate) fn with_active_descriptions(
        &self,
        tokens: &TokenTable,
        declarations: &[Arc<SyntaxDecl>],
        behaviors: &BTreeMap<Name, IdentBehavior>,
        aliases: &BTreeMap<String, Name>,
    ) -> Result<Self, CompileError> {
        let mut out = self.clone();
        out.builtin_tokens = tokens.clone();
        let mut added_categories = Vec::new();
        for (name, behavior) in behaviors {
            if !out.categories.contains_key(name) {
                added_categories.push(name.clone());
                out.categories.insert(
                    name.clone(),
                    CategoryDispatch {
                        name: name.clone(),
                        behavior: match behavior {
                            IdentBehavior::Default => LeadingIdentBehavior::Default,
                            IdentBehavior::Symbol => LeadingIdentBehavior::Symbol,
                            IdentBehavior::Both => LeadingIdentBehavior::Both,
                        },
                        leading_table: BTreeMap::new(),
                        leading_unindexed: Vec::new(),
                        trailing_table: BTreeMap::new(),
                        trailing_unindexed: Vec::new(),
                        antiquot_parser: build_category_antiquot_parser(name),
                    },
                );
            }
        }
        let first_new = out.defs.len();
        out.defs
            .reserve(declarations.len() + added_categories.len());
        for (offset, declaration) in declarations.iter().enumerate() {
            if self.def_index.contains_key(&declaration.decl) {
                return Err(CompileError::TypeMismatch {
                    owner: declaration.decl.to_display_string(),
                    detail: "active description shadows an extracted builtin parser declaration"
                        .to_owned(),
                });
            }
            out.def_index
                .insert(declaration.decl.clone(), first_new + offset);
        }
        let use_census_cache = std::ptr::eq(self, reference_builtin_interpreter());
        let census_ptrs = use_census_cache.then(census_decl_ptrs);
        let mut needs_first_tokens = Vec::new();
        let mut newly_compiled_census: Vec<(usize, usize)> = Vec::new();
        {
            let guard = use_census_cache.then(|| {
                census_compiled_cache()
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner())
            });
            for (offset, declaration) in declarations.iter().enumerate() {
                let ptr = Arc::as_ptr(declaration) as usize;
                let is_census = census_ptrs.is_some_and(|set| set.contains(&ptr));
                if is_census && let Some(cached) = guard.as_ref().and_then(|map| map.get(&ptr)) {
                    out.defs.push(cached.clone());
                    continue;
                }
                let ast = descr_ast(&declaration.descr, aliases, 0)?;
                let value = eval_ast(
                    reference_builtin_parser_table(),
                    &out.def_index,
                    &declaration.decl,
                    &ast,
                    &mut Vec::new(),
                    0,
                )?;
                let id = first_new + offset;
                out.defs.push(CompiledParser {
                    op: expect_parser(&declaration.decl, value)?,
                    first_tokens: FirstTokens::Unknown,
                });
                needs_first_tokens.push(id);
                if is_census {
                    newly_compiled_census.push((ptr, id));
                }
            }
        }
        if !needs_first_tokens.is_empty() {
            let raw_ops: Vec<_> = out
                .defs
                .iter()
                .map(|d| (Name::anonymous(), Arc::clone(&d.op)))
                .collect();
            let mut cache: Vec<_> = out
                .defs
                .iter()
                .enumerate()
                .map(|(i, d)| {
                    if needs_first_tokens.contains(&i) {
                        None
                    } else {
                        Some(d.first_tokens.clone())
                    }
                })
                .collect();
            let mut visiting = vec![false; out.defs.len()];
            for id in needs_first_tokens {
                let first = compute_def_first_tokens(id, &raw_ops, &mut cache, &mut visiting);
                out.defs[id].first_tokens = first;
            }
            if !newly_compiled_census.is_empty() {
                let mut guard = census_compiled_cache()
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                for (ptr, id) in newly_compiled_census {
                    guard.entry(ptr).or_insert_with(|| out.defs[id].clone());
                }
            }
        }
        for (offset, declaration) in declarations.iter().enumerate() {
            let id = first_new + offset;
            let Some(category) = &declaration.category else {
                continue;
            };
            let cat = out.categories.get_mut(category).ok_or_else(|| {
                CompileError::UnresolvedDecl(format!("category {}", category.to_display_string()))
            })?;
            let (table, unindexed) = if declaration.leading {
                (&mut cat.leading_table, &mut cat.leading_unindexed)
            } else {
                (&mut cat.trailing_table, &mut cat.trailing_unindexed)
            };
            // addParser conses each new entry. FileGrammar passes the actual
            // declaration/activation chronology, including local and scoped syntax.
            match out.defs[id].first_tokens.indexed_tokens() {
                Some(tokens) => {
                    for token in tokens {
                        table
                            .entry(Name::str(Name::anonymous(), token))
                            .or_default()
                            .insert(0, (id, declaration.priority));
                    }
                }
                None => unindexed.insert(0, (id, declaration.priority)),
            }
        }
        // Mirror `Lean/Elab/Syntax.lean::declareSyntaxCatQuotParser`: any newly declared
        // syntax category whose quotation opener `` `(<suffix>| `` is not yet registered in
        // `term` receives its standard `Lean.Parser.Term.quot` -> `<cat>.quot` parser.
        let term_name = Name::from_components(["term"]);
        for cat_name in added_categories {
            let LeafView::Str(suffix) = cat_name.leaf_view() else {
                continue;
            };
            let quot_sym = format!("`({suffix}|");
            let quot_key = Name::str(Name::anonymous(), &quot_sym);
            let already_registered = out
                .categories
                .get(&term_name)
                .is_some_and(|term_cat| term_cat.leading_table.contains_key(&quot_key));
            if already_registered {
                continue;
            }
            let quot_kind = Name::str(cat_name.clone(), "quot");
            let descr = Descr::Node {
                kind: Name::from_components(["Lean", "Parser", "Term", "quot"]),
                prec: MAX_PREC,
                body: Box::new(Descr::Node {
                    kind: quot_kind.clone(),
                    prec: MAX_PREC,
                    body: Box::new(Descr::Binary(
                        Name::from_components(["andthen"]),
                        Box::new(Descr::Symbol(format!("`({suffix}| "))),
                        Box::new(Descr::Binary(
                            Name::from_components(["andthen"]),
                            Box::new(Descr::Cat(cat_name.clone(), 0)),
                            Box::new(Descr::Symbol(")".to_owned())),
                        )),
                    )),
                }),
            };
            if let Ok(op) = out.compile_descr_op(&descr, aliases) {
                let id = out.defs.len();
                let first_tokens = FirstTokens::Tokens(vec![quot_sym]);
                out.defs.push(CompiledParser { op, first_tokens });
                out.def_index.entry(quot_kind).or_insert(id);
                if let Some(term_cat) = out.categories.get_mut(&term_name) {
                    term_cat
                        .leading_table
                        .entry(quot_key)
                        .or_default()
                        .insert(0, (id, 1000));
                }
            }
        }
        Ok(out)
    }

    pub(crate) fn run_description(
        &self,
        description: &Descr,
        aliases: &BTreeMap<String, Name>,
        input: ParserInput<'_>,
    ) -> ParserRun {
        let owner = Name::from_components(["active", "descriptor"]);
        let compiled = descr_ast(description, aliases, 0).and_then(|ast| {
            eval_ast(
                reference_builtin_parser_table(),
                &self.def_index,
                &owner,
                &ast,
                &mut Vec::new(),
                0,
            )
            .and_then(|value| expect_parser(&owner, value))
        });
        let op = match compiled {
            Ok(op) => op,
            Err(error) => {
                return ParserRun {
                    result: Err((input.start, ParserFailure::Description(error))),
                    next: input.start,
                    steps: 0,
                };
            }
        };
        self.run(input, |state| self.exec_op(&op, state))
    }

    pub(crate) fn run_candidates(
        &self,
        declarations: &[&SyntaxDecl],
        input: ParserInput<'_>,
    ) -> ParserRun {
        let mut candidates = Vec::with_capacity(declarations.len());
        // FileGrammar stores declaration chronology; the pin's dispatch lists
        // put the most recently registered parser first.
        for declaration in declarations.iter().rev() {
            let Some(&id) = self.def_index.get(&declaration.decl) else {
                return ParserRun {
                    result: Err((
                        input.start,
                        ParserFailure::Description(CompileError::UnresolvedDecl(
                            declaration.decl.to_display_string(),
                        )),
                    )),
                    next: input.start,
                    steps: 0,
                };
            };
            candidates.push((id, declaration.priority));
        }
        self.run(input, |state| self.longest_match(None, &candidates, state))
    }

    fn run(&self, input: ParserInput<'_>, parse: impl FnOnce(&mut RuntimeState<'_>)) -> ParserRun {
        let mut state = RuntimeState::new(input.source, false, input.max_steps);
        state.pos = input.start;
        state.ctx.saved_pos = input.saved_pos;
        state.ctx.quot_depth = input.quot_depth;
        state.ctx.prec = input.precedence;
        parse(&mut state);
        // Resource and recovered diagnostics are sticky even if a recovery,
        // optional parser or longest-match alternative cleared `error`.
        let result = if state.depth_exhausted || state.budget_exhausted {
            Err((
                state.pos,
                ParserFailure::Resource(if state.depth_exhausted {
                    ParserResourceLimit::Depth
                } else {
                    ParserResourceLimit::Steps
                }),
            ))
        } else if let Some(error) = state.recovered_errors.first() {
            Err((
                error.pos,
                ParserFailure::Recovered {
                    unexpected: error.unexpected.clone(),
                    expected: error.expected.clone(),
                },
            ))
        } else if let Some(error) = state.error.as_ref() {
            Err((
                error.pos,
                ParserFailure::Syntax {
                    unexpected: error.unexpected.clone(),
                    expected: error.expected.clone(),
                },
            ))
        } else {
            Ok(state.stack)
        };
        ParserRun {
            result,
            next: state.pos,
            steps: state.steps,
        }
    }
}
