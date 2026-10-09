//! Bounded native proof scripts, preserving real token leaves and separators.
//!
//! Tactic arguments use the ordinary term driver. Local declarations own their
//! nested `by` blocks through the heap sequence planner; they never recursively
//! call this parser on source-controlled nesting depth. A `by` inside a tactic's
//! term argument (`exact ⟨h, by rfl⟩`) does re-enter [`parse`] on the native
//! stack, so such blocks nest at most [`PROOF_NESTING`] deep.

use super::*;
use std::cell::Cell;
use std::ops::Range;
mod elimination;
pub(super) use elimination::calculation;
mod locations;
mod rcases;

/// Proof blocks open on one thread at once; the next is refused rather than recursed into on
/// a small host stack. A count, not a stack measurement, so the refusal is the same on every
/// host and build.
const PROOF_NESTING: usize = 8;

thread_local! {
    static OPEN_PROOFS: Cell<usize> = const { Cell::new(0) };
}

/// One open [`parse`] call, closed when dropped.
struct OpenProof;

impl OpenProof {
    fn enter(
        view: &SourceView,
        tokens: &[LexedToken],
        by: usize,
    ) -> Result<Self, NatDefinitionParseError> {
        OPEN_PROOFS.with(|open| {
            if open.get() >= PROOF_NESTING {
                return Err(refusal(view, tokens, by));
            }
            open.set(open.get() + 1);
            Ok(OpenProof)
        })
    }
}

impl Drop for OpenProof {
    fn drop(&mut self) {
        OPEN_PROOFS.with(|open| open.set(open.get() - 1));
    }
}

fn refusal(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::Tactic,
    }
}

/// The tactic sequence of a `decreasing_by` clause, `range` after its keyword, bounded as a
/// proof block is.
pub(super) fn tactic_sequence(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    keyword: usize,
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let _open = OpenProof::enter(view, tokens, keyword)?;
    if range.is_empty() {
        return Err(refusal(view, tokens, range.start));
    }
    elimination::sequence(leaves, view, tokens, range)
}

pub(super) fn parse(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    by: usize,
    limit: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    let _open = OpenProof::enter(view, tokens, by)?;
    let mut depth = 0_usize;
    let mut forall_commas = 0_usize;
    // A `match` header's discriminants (`match a, b with`) and a row's patterns (`| 0, _ =>`)
    // are separated by commas of their own.
    let mut match_headers = 0_usize;
    let mut matched = false;
    let mut in_patterns = false;
    let mut end = by + 1;
    while end < limit {
        match &tokens[end].kind {
            TokenKind::Symbol(symbol)
                if matches!(
                    crate::canonical_bracket(symbol.as_str()),
                    "(" | "[" | "{" | ".{" | "⦃" | "⟨"
                ) =>
            {
                depth += 1
            }
            TokenKind::Symbol(symbol)
                if matches!(
                    crate::canonical_bracket(symbol.as_str()),
                    ")" | "]" | "}" | "⦄" | "⟩"
                ) =>
            {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            TokenKind::Symbol(symbol)
                if matches!(symbol.as_str(), "forall" | "∀" | "∃") && depth == 0 =>
            {
                forall_commas += 1
            }
            TokenKind::Symbol(symbol) if symbol == "match" && depth == 0 => match_headers += 1,
            TokenKind::Symbol(symbol) if symbol == "with" && depth == 0 && match_headers > 0 => {
                match_headers -= 1;
                matched = true;
            }
            TokenKind::Symbol(symbol) if symbol == "|" && depth == 0 && matched => {
                in_patterns = true;
            }
            TokenKind::Symbol(symbol) if (symbol == "=>" || symbol == "↦") && depth == 0 => {
                in_patterns = false;
            }
            TokenKind::Symbol(symbol)
                if symbol == "," && depth == 0 && (match_headers > 0 || in_patterns) => {}
            TokenKind::Symbol(symbol) if symbol == "," && depth == 0 => {
                if forall_commas == 0 {
                    break;
                }
                forall_commas -= 1;
            }
            _ => {}
        }
        end += 1;
    }
    if depth != 0 {
        return Err(refusal(view, tokens, end));
    }
    let first = by + 1;
    if first == end {
        let sequence = Syntax::node(
            parser_kind(&["Tactic", "tacticSeq"]),
            vec![Syntax::node(
                parser_kind(&["Tactic", "tacticSeq1Indented"]),
                vec![Syntax::node(
                    Name::str(Name::anonymous(), "null"),
                    Vec::new(),
                )],
            )],
        );
        return Ok((
            Syntax::node(
                parser_kind(&["Term", "byTactic"]),
                vec![leaves.leaf(by)?, sequence],
            ),
            end,
        ));
    }
    let source = view.normalized();
    let first_line = source.line_of(tokens[first].extent.start());
    let first_column = tokens[first].extent.start().0
        - source.line_start(first_line).expect("token line exists").0;
    let by_line = source.line_of(tokens[by].extent.start());
    let by_column =
        tokens[by].extent.start().0 - source.line_start(by_line).expect("by line exists").0;
    if first_line != by_line && first_column <= by_column {
        // For declaration bodies Lean compares indentation with the declaration
        // baseline, not the inline `by` column. Accept the common indented body
        // but reject a first tactic at the beginning of a fresh line.
        if first_column == 0 {
            return Err(refusal(view, tokens, first));
        }
    }
    let sequence = elimination::sequence(leaves, view, tokens, first..end)?;
    Ok((
        Syntax::node(
            parser_kind(&["Term", "byTactic"]),
            vec![leaves.leaf(by)?, sequence],
        ),
        end,
    ))
}

fn tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let keyword = match &tokens[start].kind {
        TokenKind::Ident(name) => [
            "intro",
            "revert",
            "generalize",
            "exact",
            "assumption",
            "solve_by_elim",
            "apply",
            "refine",
            "constructor",
            "left",
            "right",
            "rfl",
            "symm",
            "change",
            "rw",
            "rewrite",
            "simp",
            "simp_all",
            "simpa",
            "subst",
            "injection",
            "contradiction",
            "by_cases",
            "decide",
            "skip",
            "fail",
            "omega",
            "unfold",
            "split",
            "rwa",
            "intros",
            "rename_i",
            "trivial",
            "obtain",
            "rcases",
            "rintro",
            "congr",
            "dsimp",
            "funext",
            "ext",
            "specialize",
            "grind",
        ]
        .into_iter()
        .find(|word| name == &Name::from_components([*word]))
        .ok_or_else(|| refusal(view, tokens, start))?,
        // `suffices` is a keyword token, not an identifier.
        TokenKind::Symbol(symbol) if symbol == "suffices" => "suffices",
        _ => return Err(refusal(view, tokens, start)),
    };
    // Tactic words are contextual: `def apply ...` must stay a legal identifier.
    // The selected tactic production gives its keyword an atom leaf.
    let leaf = leaves.leaf(start)?;
    let atom = Syntax::Atom {
        info: leaf.info(),
        val: keyword.to_string(),
    };
    match keyword {
        "simp" | "dsimp" => simplify(leaves, view, tokens, range, atom, keyword),
        "simp_all" => simplify_all(leaves, view, tokens, range, atom),
        "simpa" => simpa(leaves, view, tokens, range, atom),
        "rw" | "rewrite" | "rwa" => rewrite(leaves, view, tokens, range, atom, keyword),
        "unfold" | "split" => located(leaves, view, tokens, range, atom, keyword),
        "obtain" | "rcases" | "rintro" | "ext" => {
            rcases::tactic(leaves, view, tokens, range, keyword, atom)
        }
        "generalize" => generalize(leaves, view, tokens, range, atom),
        "by_cases" => by_cases(leaves, view, tokens, range, atom),
        "suffices" => suffices(leaves, view, tokens, range, atom),
        "change" => change(leaves, view, tokens, range, atom),
        // `"specialize " term` (`Init/Tactics.lean`) has `exact`'s shape.
        "exact" | "apply" | "refine" | "specialize" => {
            term_tactic(leaves, view, tokens, range, keyword, atom)
        }
        _ => local_tactic(leaves, view, tokens, range, keyword, atom),
    }
}

// Separate argument productions keep their debug-build stack frames out of
// the common dispatch path, especially while the term driver is active.
#[inline(never)]
fn local_tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: &str,
    atom: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let mut args = vec![atom];
    match keyword {
        "symm" if range.end == start + 1 => {
            args.push(null_node(Vec::new()));
        }
        "revert" if range.end > start + 1 => {
            let mut names = Vec::new();
            for index in start + 1..range.end {
                if !matches!(&tokens[index].kind, TokenKind::Ident(_)) {
                    return Err(refusal(view, tokens, index));
                }
                names.push(leaves.leaf(index)?);
            }
            args.push(null_node(names));
        }
        // `syntax (name := congr) "congr" (ppSpace num)? : tactic` (`Init/Tactics.lean`).
        "congr" if range.end <= start + 2 => {
            let depth = if range.end == start + 2 {
                if !matches!(
                    &tokens[start + 1].kind,
                    TokenKind::Literal(LiteralKind::Nat)
                ) {
                    return Err(refusal(view, tokens, start + 1));
                }
                vec![Syntax::node(
                    Name::str(Name::anonymous(), "num"),
                    vec![leaves.leaf(start + 1)?],
                )]
            } else {
                Vec::new()
            };
            args.push(null_node(depth));
        }
        // `syntax "funext" (ppSpace colGt term:max)* : tactic` (`Init/Tactics.lean`), a root
        // kind; only names and holes are read.
        "funext" => {
            let mut names = Vec::new();
            for index in start + 1..range.end {
                names.push(match &tokens[index].kind {
                    TokenKind::Ident(_) => leaves.leaf(index)?,
                    TokenKind::Symbol(symbol) if symbol == "_" => {
                        Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(index)?])
                    }
                    _ => return Err(refusal(view, tokens, index)),
                });
            }
            args.push(null_node(names));
            return Ok(Syntax::node(
                Name::from_components(["tacticFunext___"]),
                args,
            ));
        }
        // `syntax (name := renameI) "rename_i" (ppSpace colGt binderIdent)+ : tactic`
        // (`Init/Tactics.lean`).
        "rename_i" if range.end > start + 1 => {
            let mut names = Vec::new();
            for index in start + 1..range.end {
                let name = match &tokens[index].kind {
                    TokenKind::Ident(_) => leaves.leaf(index)?,
                    TokenKind::Symbol(symbol) if symbol == "_" => {
                        Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(index)?])
                    }
                    _ => return Err(refusal(view, tokens, index)),
                };
                names.push(Syntax::node(
                    Name::from_components(["Lean", "binderIdent"]),
                    vec![name],
                ));
            }
            args.push(null_node(names));
        }
        // `intros` is `"intros" (ppSpace colGt (ident <|> hole))*` (`Init/Tactics.lean`).
        "intro" | "intros" => {
            let mut names = Vec::new();
            for index in start + 1..range.end {
                if matches!(&tokens[index].kind, TokenKind::Ident(_)) {
                    names.push(leaves.leaf(index)?);
                } else if matches!(&tokens[index].kind, TokenKind::Symbol(symbol) if symbol == "_")
                {
                    names.push(Syntax::node(
                        parser_kind(&["Term", "hole"]),
                        vec![leaves.leaf(index)?],
                    ));
                } else {
                    return Err(refusal(view, tokens, index));
                }
            }
            args.push(null_node(names));
        }
        "injection"
            if range.end >= start + 2 && matches!(&tokens[start + 1].kind, TokenKind::Ident(_)) =>
        {
            args.push(leaves.leaf(start + 1)?);
            let mut names = Vec::new();
            if range.end > start + 2 {
                if !matches!(&tokens[start + 2].kind, TokenKind::Symbol(s) if s == "with")
                    || range.end == start + 3
                {
                    return Err(refusal(view, tokens, start + 2));
                }
                for at in start + 3..range.end {
                    if !matches!(&tokens[at].kind, TokenKind::Ident(_))
                        && !matches!(&tokens[at].kind, TokenKind::Symbol(s) if s == "_")
                    {
                        return Err(refusal(view, tokens, at));
                    }
                    names.push(leaves.leaf(at)?);
                }
                // Keep the actual `with` leaf for lossless syntax reconstruction.
                args.push(null_node(vec![leaves.leaf(start + 2)?, null_node(names)]));
            } else {
                args.push(null_node(Vec::new()));
            }
        }
        "subst"
            if range.end >= start + 2
                && (start + 1..range.end)
                    .all(|at| matches!(&tokens[at].kind, TokenKind::Ident(_))) =>
        {
            // `"subst" (colGt term:max)+` (`Init/Tactics.lean`): the names are a list.
            args.push(null_node(
                (start + 1..range.end)
                    .map(|at| leaves.leaf(at))
                    .collect::<Result<Vec<_>, _>>()?,
            ));
        }
        // `grind` with its configuration flags only: `"grind" optConfig (&" only")?
        // (" [" grindParam,* "]")? ("=> " grindSeq)?` (`Init/Grind/Tactics.lean`).
        "grind" => {
            let (config, end) = config(leaves, tokens, start + 1, range.end)?;
            if end != range.end {
                return Err(refusal(view, tokens, end));
            }
            args.extend([
                config,
                null_node(Vec::new()),
                null_node(Vec::new()),
                null_node(Vec::new()),
            ]);
        }
        "fail"
            if range.end == start + 2
                && matches!(
                    &tokens[start + 1].kind,
                    TokenKind::Literal(LiteralKind::Str)
                ) =>
        {
            args.push(leaves.leaf(start + 1)?);
        }
        // `decide` and `omega` are `"…" optConfig` (`Init/Tactics.lean`); the empty
        // configuration is a node of its own in the pin's tree.
        "decide" | "omega" => {
            let (config, end) = config(leaves, tokens, start + 1, range.end)?;
            if end != range.end {
                return Err(refusal(view, tokens, end));
            }
            args.push(config);
        }
        "assumption" | "solve_by_elim" | "rfl" | "contradiction" | "constructor" | "left"
        | "right" | "skip" | "fail" | "trivial"
            if range.end == start + 1 => {}
        _ => return Err(refusal(view, tokens, start)),
    }
    // `rfl` is `macro "rfl" : tactic` in `Init/Tactics.lean`, whose kind is `tacticRfl`.
    let kind = match keyword {
        "rfl" => "tacticRfl",
        // `macro "trivial" : tactic` (`Init/Tactics.lean`).
        "trivial" => "tacticTrivial",
        "rename_i" => "renameI",
        _ => keyword,
    };
    Ok(Syntax::node(parser_kind(&["Tactic", kind]), args))
}

/// `macro "suffices " d:sufficesDecl : tactic` (`Init/Tactics.lean`), where `sufficesDecl` is
/// `(atomic (group (binderIdent " : ")) <|> hygieneInfo) term (fromTerm <|> byTactic')`.
#[inline(never)]
fn suffices(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let named = range.end > start + 3
        && matches!(&tokens[start + 1].kind, TokenKind::Ident(_))
        && matches!(&tokens[start + 2].kind, TokenKind::Symbol(s) if s == ":");
    let binder = if named {
        Syntax::node(
            Name::from_components(["group"]),
            vec![leaves.leaf(start + 1)?, leaves.leaf(start + 2)?],
        )
    } else {
        hygiene_info_following(&leaves.leaf(start)?)
    };
    let type_start = if named { start + 3 } else { start + 1 };
    let mut depth = 0usize;
    let mut intro = None;
    for at in type_start..range.end {
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
        if depth == 0
            && (crate::term_locals::word(tokens, at, "from")
                || crate::term_locals::word(tokens, at, "by"))
        {
            intro = Some(at);
            break;
        }
    }
    let intro = match intro {
        Some(intro) if intro > type_start && intro + 1 < range.end => intro,
        _ => return Err(refusal(view, tokens, start)),
    };
    let type_ = bounded_term(
        leaves,
        view,
        tokens,
        type_start..intro,
        DefinitionGrammar::Scalar,
    )?;
    let rhs = if crate::term_locals::word(tokens, intro, "by") {
        let mut proof = bounded_term(
            leaves,
            view,
            tokens,
            intro..range.end,
            DefinitionGrammar::Scalar,
        )?;
        match &mut proof {
            Syntax::Node { kind, .. } if *kind == parser_kind(&["Term", "byTactic"]) => {
                *kind = parser_kind(&["Term", "byTactic'"]);
            }
            _ => return Err(refusal(view, tokens, intro)),
        }
        proof
    } else {
        let leaf = leaves.leaf(intro)?;
        Syntax::node(
            parser_kind(&["Term", "fromTerm"]),
            vec![
                Syntax::Atom {
                    info: leaf.info(),
                    val: "from".to_string(),
                },
                bounded_term(
                    leaves,
                    view,
                    tokens,
                    intro + 1..range.end,
                    DefinitionGrammar::Scalar,
                )?,
            ],
        )
    };
    Ok(Syntax::node(
        parser_kind(&["Tactic", "tacticSuffices_"]),
        vec![
            keyword,
            Syntax::node(
                parser_kind(&["Term", "sufficesDecl"]),
                vec![binder, type_, rhs],
            ),
        ],
    ))
}

#[inline(never)]
fn term_tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: &str,
    atom: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    if range.len() < 2 {
        return Err(refusal(view, tokens, range.start));
    }
    let term = bounded_term(
        leaves,
        view,
        tokens,
        range.start + 1..range.end,
        DefinitionGrammar::Scalar,
    )?;
    Ok(Syntax::node(
        parser_kind(&["Tactic", keyword]),
        vec![atom, term],
    ))
}

#[inline(never)]
fn change(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    atom: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    if range.len() < 2 {
        return Err(refusal(view, tokens, range.start));
    }
    let target = bounded_term(
        leaves,
        view,
        tokens,
        range.start + 1..range.end,
        DefinitionGrammar::Scalar,
    )?;
    Ok(Syntax::node(
        parser_kind(&["Tactic", "change"]),
        vec![atom, target, null_node(Vec::new())],
    ))
}

#[inline(never)]
fn by_cases(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    if range.len() < 2 {
        return Err(refusal(view, tokens, start));
    }
    let named = range.len() > 3
        && matches!(&tokens[start + 1].kind, TokenKind::Ident(_))
        && matches!(&tokens[start + 2].kind, TokenKind::Symbol(s) if s == ":");
    let term = bounded_term(
        leaves,
        view,
        tokens,
        start + if named { 3 } else { 1 }..range.end,
        DefinitionGrammar::Scalar,
    )?;
    let witness = null_node(if named {
        vec![leaves.leaf(start + 1)?, leaves.leaf(start + 2)?]
    } else {
        Vec::new()
    });
    // `syntax "by_cases " (atomic(ident " : "))? term : tactic` (`Init/ByCases.lean`): a root
    // kind, `«tacticBy_cases_:_»`.
    Ok(Syntax::node(
        Name::from_components(["tacticBy_cases_:_"]),
        vec![keyword, witness, term],
    ))
}

// Keep this production's syntax temporaries out of the common tactic frame.
// In debug builds that frame remains live across the heap-driven term parser;
// growing it can overflow even a nonrecursive parse on a small thread stack.
#[inline(never)]
fn generalize(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    if range.len() < 4 {
        return Err(refusal(view, tokens, start));
    }
    let named = matches!(&tokens[start + 1].kind, TokenKind::Ident(_))
        && matches!(&tokens[start + 2].kind, TokenKind::Symbol(s) if s == ":");
    let expression = start + if named { 3 } else { 1 };
    let equality = range.end - 2;
    if expression >= equality
        || !matches!(&tokens[equality].kind, TokenKind::Symbol(s) if s == "=")
        || !matches!(&tokens[range.end - 1].kind, TokenKind::Ident(_))
    {
        return Err(refusal(view, tokens, start));
    }
    let term = bounded_term(
        leaves,
        view,
        tokens,
        expression..equality,
        DefinitionGrammar::Scalar,
    )?;
    let witness = null_node(if named {
        vec![leaves.leaf(start + 1)?, leaves.leaf(start + 2)?]
    } else {
        Vec::new()
    });
    Ok(Syntax::node(
        parser_kind(&["Tactic", "generalize"]),
        vec![
            keyword,
            witness,
            term,
            leaves.leaf(equality)?,
            leaves.leaf(range.end - 1)?,
        ],
    ))
}

fn rewrite(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
    form: &str,
) -> Result<Syntax, NatDefinitionParseError> {
    let (range, location) = locations::split(leaves, view, tokens, range)?;
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    if range.len() < 4 || !is(range.start + 1, "[") || !is(range.end - 1, "]") {
        return Err(refusal(view, tokens, range.start));
    }
    let mut rows = Vec::new();
    let mut start = range.start + 2;
    let mut depth = 0_usize;
    for at in (range.start + 2)..range.end {
        let end = at == range.end - 1;
        if end || (depth == 0 && is(at, ",")) {
            if at == start {
                if end && !rows.is_empty() {
                    break;
                }
                return Err(refusal(view, tokens, at));
            }
            let reverse = is(start, "←") || is(start, "<-");
            let term_start = start + usize::from(reverse);
            let direction = if reverse {
                null_node(vec![leaves.leaf(start)?])
            } else {
                null_node(Vec::new())
            };
            let term = bounded_term(
                leaves,
                view,
                tokens,
                term_start..at,
                DefinitionGrammar::Scalar,
            )?;
            rows.push(Syntax::node(
                parser_kind(&["Tactic", "rwRule"]),
                vec![direction, term],
            ));
            if !end {
                rows.push(leaves.leaf(at)?);
            }
            start = at + 1;
        } else if is(at, "(") || is(at, ".{") {
            depth += 1;
        } else if is(at, ")") || is(at, "}") {
            depth = depth
                .checked_sub(1)
                .ok_or_else(|| refusal(view, tokens, at))?;
        }
    }
    if depth != 0 {
        return Err(refusal(view, tokens, range.end));
    }
    let rules = Syntax::node(
        parser_kind(&["Tactic", "rwRuleSeq"]),
        vec![
            leaves.leaf(range.start + 1)?,
            null_node(rows),
            leaves.leaf(range.end - 1)?,
        ],
    );
    Ok(match form {
        // `macro "rwa " rws:rwRuleSeq loc:(location)? : tactic` (`Init/Tactics.lean`) takes no
        // configuration.
        "rwa" => Syntax::node(
            parser_kind(&["Tactic", "tacticRwa__"]),
            vec![keyword, rules, location],
        ),
        _ => Syntax::node(
            parser_kind(&["Tactic", if form == "rw" { "rwSeq" } else { "rewriteSeq" }]),
            vec![keyword, default_config(), rules, location],
        ),
    })
}

/// `"unfold" (ppSpace colGt ident)+ (location)?` and `"split" (ppSpace colGt term)?
/// (location)?` (`Init/Tactics.lean`).
#[inline(never)]
fn located(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
    form: &str,
) -> Result<Syntax, NatDefinitionParseError> {
    let (range, location) = locations::split(leaves, view, tokens, range)?;
    let arguments = range.start + 1..range.end;
    let argument = if form == "unfold" {
        if arguments.is_empty() {
            return Err(refusal(view, tokens, range.start));
        }
        let mut names = Vec::new();
        for at in arguments {
            if !matches!(&tokens[at].kind, TokenKind::Ident(_)) {
                return Err(refusal(view, tokens, at));
            }
            names.push(leaves.leaf(at)?);
        }
        null_node(names)
    } else if arguments.is_empty() {
        null_node(Vec::new())
    } else {
        null_node(vec![bounded_term(
            leaves,
            view,
            tokens,
            arguments,
            DefinitionGrammar::Scalar,
        )?])
    };
    Ok(Syntax::node(
        parser_kind(&["Tactic", form]),
        vec![keyword, argument, location],
    ))
}

/// The empty configuration of a tactic that takes `optConfig` (`decide`, `simp`, `simp_all`,
/// `rw`, `rewrite`; vendored `src/Init/Tactics.lean`): a node of its own in the pin's tree.
fn default_config() -> Syntax {
    Syntax::node(
        parser_kind(&["Tactic", "optConfig"]),
        vec![null_node(Vec::new())],
    )
}

/// `optConfig := (colGt configItem)*` (`Init/Tactics.lean`) from `start`: the flags `+x`
/// (`posConfigItem`) and `-x` (`negConfigItem`), each sign touching its name; a
/// `(x := v)` item is not read. Returns the node and the first token after it.
fn config(
    leaves: &Leaves,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    let mut items = Vec::new();
    let mut at = start;
    while at + 1 < end
        && matches!(&tokens[at].kind, TokenKind::Symbol(s) if s == "+" || s == "-")
        && matches!(&tokens[at + 1].kind, TokenKind::Ident(_))
        && tokens[at].extent.end() == tokens[at + 1].extent.start()
    {
        let kind = if matches!(&tokens[at].kind, TokenKind::Symbol(s) if s == "+") {
            "posConfigItem"
        } else {
            "negConfigItem"
        };
        items.push(Syntax::node(
            parser_kind(&["Tactic", "configItem"]),
            vec![Syntax::node(
                parser_kind(&["Tactic", kind]),
                vec![leaves.leaf(at)?, leaves.leaf(at + 1)?],
            )],
        ));
        at += 2;
    }
    Ok((
        Syntax::node(
            parser_kind(&["Tactic", "optConfig"]),
            vec![null_node(items)],
        ),
        at,
    ))
}

/// Whole-context simplification shares rule syntax with simp, but has no
/// location suffix. Retain the original keyword and all source attachments.
#[inline(never)]
fn simplify_all(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let end = range.end;
    let mut parsed = simplify(leaves, view, tokens, range, keyword, "simp")?;
    let Syntax::Node { kind, args, .. } = &mut parsed else {
        unreachable!("simplify builds a tactic node");
    };
    if !matches!(&args[5], Syntax::Node { args, .. } if args.is_empty()) {
        return Err(refusal(view, tokens, end));
    }
    *kind = parser_kind(&["Tactic", "simpAll"]);
    args.pop();
    Ok(parsed)
}

/// Separate a top-level evidence clause without splitting identifiers inside
/// selected rules or the evidence term. The prefix shares the simp grammar.
#[inline(never)]
fn simpa(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut depth = 0usize;
    let mut using_at = None;
    for at in range.start + 1..range.end {
        match &tokens[at].kind {
            TokenKind::Symbol(s)
                if matches!(
                    crate::canonical_bracket(s.as_str()),
                    "(" | "[" | "{" | ".{" | "⦃" | "⟨"
                ) =>
            {
                depth += 1
            }
            TokenKind::Symbol(s)
                if matches!(
                    crate::canonical_bracket(s.as_str()),
                    ")" | "]" | "}" | "⦄" | "⟩"
                ) =>
            {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| refusal(view, tokens, at))?;
            }
            // `using` is a token at the pin, so an escaped `«using»` is an identifier and never this.
            // `using!` (`simpaUsingBang`): the close at default transparency, a token too.
            TokenKind::Symbol(s) if depth == 0 && (s == "using" || s == "using!") => {
                using_at = Some(at);
                break;
            }
            _ => {}
        }
    }
    let prefix_end = using_at.unwrap_or(range.end);
    let bang = using_at
        .is_some_and(|at| matches!(&tokens[at].kind, TokenKind::Symbol(s) if s == "using!"));
    let using = if let Some(at) = using_at {
        let term = bounded_term(
            leaves,
            view,
            tokens,
            at + 1..range.end,
            DefinitionGrammar::Scalar,
        )?;
        let leaf = leaves.leaf(at)?;
        null_node(vec![
            Syntax::Atom {
                info: leaf.info(),
                val: if bang { "using!" } else { "using" }.into(),
            },
            term,
        ])
    } else {
        null_node(Vec::new())
    };
    let mut parsed = simplify(
        leaves,
        view,
        tokens,
        range.start..prefix_end,
        keyword,
        "simp",
    )?;
    let Syntax::Node { kind, args, .. } = &mut parsed else {
        unreachable!("simplify builds a tactic node");
    };
    if !matches!(&args[5], Syntax::Node { args, .. } if args.is_empty()) {
        return Err(refusal(view, tokens, prefix_end));
    }
    // `simpa := "simpa" "?"? "!"? simpaArgsRest` and `simpaArgsRest := optConfig
    // (discharger)? (&" only")? (simpArgs)? (" using " term)?` (`Init/Tactics.lean`).
    *kind = parser_kind(&["Tactic", "simpa"]);
    let mut slots = std::mem::take(args).into_iter();
    let keyword = slots.next().expect("simp keyword");
    let mut rest: Vec<Syntax> = slots.take(4).collect();
    // Its rule list is a `simpArgs` node of its own (`(ppSpace simpArgs)?`), where `simp`
    // writes the brackets inline.
    if let Syntax::Node { args: list, .. } = &mut rest[3]
        && list.len() == 3
    {
        let inline = std::mem::take(list);
        *list = vec![Syntax::node(parser_kind(&["Tactic", "simpArgs"]), inline)];
    }
    // `simpaUsingBangArgsRest` ends in its mandatory `"using!" term`, not an optional group.
    if bang {
        let mut using = using;
        let Syntax::Node { args: clause, .. } = &mut using else {
            unreachable!("the using clause is a node");
        };
        rest.extend(std::mem::take(clause));
        *kind = parser_kind(&["Tactic", "simpaUsingBang"]);
    } else {
        rest.push(using);
    }
    *args = vec![
        keyword,
        null_node(Vec::new()),
        null_node(Vec::new()),
        Syntax::node(
            parser_kind(&[
                "Tactic",
                if bang {
                    "simpaUsingBangArgsRest"
                } else {
                    "simpaArgsRest"
                },
            ]),
            rest,
        ),
    ];
    Ok(parsed)
}

/// Simplification with either an explicit-only set or the environment's native
/// simp registry. The optional `only` leaf remains visible in the syntax tree.
///
/// `dsimp` has `simp`'s slots, its rules `simpErase <|> simpLemma` (no `*`).
fn simplify(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
    kind: &str,
) -> Result<Syntax, NatDefinitionParseError> {
    let (range, location) = locations::split(leaves, view, tokens, range)?;
    let (config, at) = config(leaves, tokens, range.start + 1, range.end)?;
    let has_only = at < range.end
        && matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(name)) if name == &Name::from_components(["only"]));
    let only = if has_only {
        let leaf = leaves.leaf(at)?;
        null_node(vec![Syntax::Atom {
            info: leaf.info(),
            val: "only".to_string(),
        }])
    } else {
        null_node(Vec::new())
    };
    let open = at + usize::from(has_only);
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    let arguments = if open == range.end {
        null_node(Vec::new())
    } else {
        if range.end < open + 2 || !is(open, "[") || !is(range.end - 1, "]") {
            return Err(refusal(view, tokens, open));
        }
        let mut rows = Vec::new();
        let mut start = open + 1;
        let mut depth = 0_usize;
        for at in open + 1..range.end {
            let end = at == range.end - 1;
            if end || depth == 0 && is(at, ",") {
                if at == start {
                    if end && (start == open + 1 || !rows.is_empty()) {
                        break;
                    }
                    return Err(refusal(view, tokens, at));
                }
                let rule = if is(start, "*") {
                    if at != start + 1 || kind == "dsimp" {
                        return Err(refusal(view, tokens, start + 1));
                    }
                    Syntax::node(
                        parser_kind(&["Tactic", "simpStar"]),
                        vec![leaves.leaf(start)?],
                    )
                } else if is(start, "-") {
                    if at != start + 2 || !matches!(tokens[start + 1].kind, TokenKind::Ident(_)) {
                        return Err(refusal(view, tokens, start + 1));
                    }
                    Syntax::node(
                        parser_kind(&["Tactic", "simpErase"]),
                        vec![leaves.leaf(start)?, leaves.leaf(start + 1)?],
                    )
                } else {
                    let reverse = is(start, "←") || is(start, "<-");
                    let direction = if reverse {
                        null_node(vec![leaves.leaf(start)?])
                    } else {
                        null_node(Vec::new())
                    };
                    let term = bounded_term(
                        leaves,
                        view,
                        tokens,
                        start + usize::from(reverse)..at,
                        DefinitionGrammar::Scalar,
                    )?;
                    Syntax::node(
                        parser_kind(&["Tactic", "simpLemma"]),
                        vec![null_node(Vec::new()), direction, term],
                    )
                };
                rows.push(rule);
                if !end {
                    rows.push(leaves.leaf(at)?);
                }
                start = at + 1;
            } else if is(at, "(") || is(at, ".{") {
                depth += 1;
            } else if is(at, ")") || is(at, "}") {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| refusal(view, tokens, at))?;
            }
        }
        if depth != 0 {
            return Err(refusal(view, tokens, range.end));
        }
        null_node(vec![
            leaves.leaf(open)?,
            null_node(rows),
            leaves.leaf(range.end - 1)?,
        ])
    };
    Ok(Syntax::node(
        parser_kind(&["Tactic", kind]),
        vec![
            keyword,
            config,
            null_node(Vec::new()),
            only,
            arguments,
            location,
        ],
    ))
}

#[cfg(test)]
mod simp_tests {
    use super::*;

    #[test]
    fn ordinary_simp_preserves_source_and_an_absent_only_marker() {
        for tail in [
            "simp",
            "simp []",
            "simp [h, <- k]",
            "simp at h",
            "simp [h] at hx ⊢",
        ] {
            let source = format!("theorem t (x : Nat) : x = x := by\r\n  /- 🦀 -/ {tail}\r\n");
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
            let mut pending = vec![parsed.syntax()];
            let mut count = 0;
            while let Some(node) = pending.pop() {
                if let Syntax::Node { kind, args, .. } = node {
                    if kind == &parser_kind(&["Tactic", "simp"]) {
                        assert_eq!(args.len(), 6);
                        assert!(matches!(&args[3], Syntax::Node { args, .. } if args.is_empty()));
                        count += 1;
                    }
                    pending.extend(args);
                }
            }
            assert_eq!(count, 1);
        }
    }

    #[test]
    fn simp_only_accepts_empty_ordered_reverse_and_multiline_rule_lists() {
        for source in [
            "theorem t (x : Nat) : x = x := by simp only []",
            "theorem t (x : Nat) : x = x := by simp only",
            "theorem t (x : Nat) : x = x := by simp only [h, <- k,]",
            "theorem t (x : Nat) : x = x := by\n  simp only [h,\n    <- k]\n  exact p",
        ] {
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            let mut pending = vec![&parsed.syntax];
            let mut found = false;
            while let Some(syntax) = pending.pop() {
                if let Syntax::Node { kind, args, .. } = syntax {
                    if kind == &parser_kind(&["Tactic", "simp"]) {
                        assert_eq!(args.len(), 6);
                        assert!(
                            matches!(&args[3], Syntax::Node { args, .. } if matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "only"))
                        );
                        found = true;
                    }
                    pending.extend(args);
                }
            }
            assert!(found);
        }
    }

    #[test]
    fn simp_erasures_preserve_structural_names_direction_and_original_leaves() {
        for tail in [
            "simp [-h]",
            "simp only [-h, h, -h, ← k]",
            "simp [h, /- 🦀 -/ -N.«a.b»,\r\n    <- k,] at hx ⊢",
            "simp [-_root_.N.h, -«-», -«simp»]",
        ] {
            let source = format!("theorem t (n : Nat) : n = n := by\r\n  {tail}\r\n");
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
            let mut pending = vec![parsed.syntax()];
            let mut erasures = 0;
            while let Some(node) = pending.pop() {
                if let Syntax::Node { kind, args, .. } = node {
                    if kind == &parser_kind(&["Tactic", "simpErase"]) {
                        assert!(
                            matches!(args.as_slice(), [Syntax::Atom { val, .. }, Syntax::Ident { .. }] if val == "-")
                        );
                        erasures += 1;
                    }
                    pending.extend(args);
                }
            }
            assert!(erasures > 0);
        }
    }

    #[test]
    fn simp_wildcards_preserve_original_leaves_and_are_not_identifier_names() {
        for tactic in [
            "simp [*]",
            "simp only [*, *]",
            "simp [h, /- 🦀 -/ *,] at hx ⊢",
        ] {
            let source = format!("theorem t (P : Prop) (h : P) : P := by {tactic}\r\n");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            let mut pending = vec![parsed.syntax()];
            let mut stars = 0;
            while let Some(syntax) = pending.pop() {
                if let Syntax::Node { kind, args, .. } = syntax {
                    if kind == &parser_kind(&["Tactic", "simpStar"]) {
                        assert!(
                            matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "*")
                        );
                        stars += 1;
                    }
                    pending.extend(args);
                }
            }
            assert!(stars > 0);
        }
        assert!(
            parse_definition("theorem t (P : Prop) («*» : P) : P := by simp only [«*»]".as_bytes())
                .is_ok()
        );
    }

    #[test]
    fn unsupported_simp_features_are_not_silently_ignored() {
        for tail in [
            "subst",
            "simp only [h] at",
            "simp only [* h]",
            "simp only [← *]",
            "simp only [-*]",
            "simp only [,h]",
            "simp only [h,,k]",
            "simp only [<-]",
            "simp only [h] garbage",
            "simp [-]",
            "simp [-1]",
            "simp [-h x]",
            "simp [-(h)]",
            "simp [-← h]",
            "simp [-h.{u}]",
            "simp [-h,,k]",
        ] {
            let source = format!("theorem t (x : Nat) : x = x := by {tail}");
            assert!(parse_source_command(source.as_bytes()).is_err(), "{source}");
        }
        assert!(parse_definition(b"def simp (only : Nat) := only").is_ok());
    }
}

#[cfg(test)]
mod equality_tests {
    use super::*;
    #[test]
    fn substitution_is_contextual_and_requires_a_single_local_name() {
        assert!(parse_definition(b"def subst (x : Nat) := x").is_ok());
        for tail in ["subst h", "subst x"] {
            assert!(
                parse_source_command(
                    format!("theorem t (x y : Nat) (h : x = y) : x = y := by {tail}; rfl")
                        .as_bytes()
                )
                .is_ok()
            );
        }
        for tail in [
            "subst",
            "subst 2",
            "subst (h)",
            "subst h at x",
            "subst h, x",
        ] {
            assert!(
                parse_source_command(
                    format!("theorem t (x : Nat) : x = x := by {tail}").as_bytes()
                )
                .is_err(),
                "{tail}"
            );
        }
    }
}

#[cfg(test)]
mod constructor_equality_tests {
    use super::*;
    #[test]
    fn injection_is_contextual_and_preserves_original_syntax() {
        for source in [
            "def injection (x : Nat) := x",
            "def contradiction (x : Nat) := x",
            "theorem t (h : 0 = 1) : 0 = 1 := by contradiction",
            "theorem t (h : 0 = 1) : 0 = 1 := by injection h",
            "theorem t (h : 0 = 1) : 0 = 1 := by\r\n  injection h /- names -/ with p _ q\r\n  exact p",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }
    #[test]
    fn malformed_injections_do_not_drop_extra_tokens() {
        for tail in [
            "contradiction h",
            "contradiction with h",
            "injection",
            "injection 1",
            "injection (h)",
            "injection h with",
            "injection h at x",
            "injection h with x, y",
            "injection h with 2",
        ] {
            assert!(
                parse_definition(format!("theorem t := by {tail}").as_bytes()).is_err(),
                "{tail}"
            );
        }
    }
}

#[cfg(test)]
mod local_declaration_tests {
    use super::*;

    #[test]
    fn local_declarations_preserve_comments_newlines_and_quantified_types() {
        for source in [
            // `have` is a keyword at the pin: a declaration named `have` escapes it.
            "def «have» (n : Nat) : Nat := n",
            "theorem t (n : Nat) : n = n := by\r\n  have /- local -/ h : forall x : Nat, x = x := by\r\n    intro x\r\n    rfl -- proof\r\n  exact h n\r\n",
            "theorem t (n : Nat) : n = n := by have : n = n := rfl; exact this",
            "theorem t (n : Nat) : n = n := by have := (rfl : n = n); exact this",
            "def t : Nat := by let n : Nat := 7; exact n",
            "def t : Package := by let p : Package := { value := 7, carrier := Nat }; exact p",
            "theorem t : 0 = 0 := by\n  have h : 0 = 0 := by\n    cases flag with\n    | false => rfl\n    | true => rfl\n  exact h",
        ] {
            let parsed =
                parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
        // The bare spelling is refused, as the Reference refuses it (`expected identifier`).
        assert!(parse_definition(b"def have (n : Nat) : Nat := n").is_err());
    }

    #[test]
    fn malformed_local_declarations_never_drop_tokens() {
        for tail in [
            "have",
            "have h",
            "have h :",
            "have h :=",
            "have h : := rfl",
            "have h : Nat := by",
            "have 7 := 7",
            "let := 7",
            "let : Nat := 7",
            "let n = 7",
            "have h (x : Nat) := x",
            "have h : 0 = 0 := by\n  exact h",
        ] {
            let source = format!("theorem t : 0 = 0 := by\n  {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        // A proof nested in the value is a term the pin parses (it fails in elaboration: `rfl`
        // has no relation to close), bounded as any proof in a tactic term.
        assert!(
            parse_definition(b"theorem t : 0 = 0 := by\n  have h := (by rfl)").is_ok(),
            "a nested proof value"
        );
    }

    #[test]
    fn nested_local_proofs_use_heap_frames() {
        std::thread::Builder::new()
            .name("nested_local_proofs_use_heap_frames".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                let depth = 300;
                let mut source = String::from("theorem t : 0 = 0 := by\n");
                for i in 0..depth {
                    source.push_str(&format!("{}have h{i} : 0 = 0 := by\n", "  ".repeat(i + 1)));
                }
                source.push_str(&format!("{}rfl\n", "  ".repeat(depth + 1)));
                for i in (0..depth).rev() {
                    source.push_str(&format!("{}exact h{i}\n", "  ".repeat(i + 1)));
                }
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod construction_refinement_tests {
    use super::*;

    #[test]
    fn construction_and_holes_preserve_original_tokens_and_scopes() {
        for source in [
            "def refine (constructor left right : Nat) : Nat := constructor + left + right",
            "theorem t : Both P Q := by\r\n  constructor /- fields -/\r\n  exact p\r\n  exact q\r\n",
            "theorem t : Either P Q := by right; exact q",
            "theorem t : P := by\r\n  refine /- explicit goals -/ f ?named ?_\r\n  exact p\r\n  exact q\r\n",
            "theorem t : forall x : Nat, x = x := by refine fun x => ?_; rfl",
            "def annotated : Nat := by refine (7 : ?type); exact Nat",
        ] {
            let parsed = parse_definition(source.as_bytes())
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
    }

    #[test]
    fn decidable_case_syntax_is_lossless_and_contextual() {
        for source in [
            "def by_cases (h : Nat) : Nat := h",
            "theorem t : True := by\r\n  by_cases /- choice -/ h : Not False\r\n  · exact h\r\n  · contradiction\r\n",
            "theorem t : True := by by_cases (Not False) <;> exact True.intro",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
        for suffix in [
            "by_cases",
            "by_cases h :",
            "by_cases : True",
            "by_cases h : True extra :",
        ] {
            let source = format!("theorem t : True := by {suffix}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn decide_is_contextual_and_does_not_drop_extra_arguments() {
        for source in [
            "def decide (p : Nat) : Nat := p",
            "theorem t : True := by\r\n  decide /- checked computation -/\r\n",
            "theorem t : Both True True := by constructor <;> (decide)",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
        for tail in ["decide p", "decide 1", "decide [h]"] {
            let source = format!("theorem t : True := by {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn revert_preserves_names_comments_and_contextual_identifiers() {
        for source in [
            "def revert (x : Nat) : Nat := x",
            "theorem t : True := by revert h",
            "theorem t : True := by\r\n  revert «x.y» /- dependencies -/ h₂\r\n  intro z q",
            "theorem t : True := by first | (revert h; fail) | assumption",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
        for tail in [
            "revert",
            "revert _",
            "revert 3",
            "revert (h)",
            "revert h, k",
        ] {
            let source = format!("theorem t : True := by {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn generalize_preserves_the_expression_and_optional_equality_name() {
        for source in [
            "def generalize (x : Nat) : Nat := x",
            "theorem t : True := by generalize f x = y",
            "theorem t : True := by\r\n  generalize «eq.h» /- witness -/ : (f x) = «new.x»\r\n  assumption",
            "theorem t : True := by first | (generalize 3 = x; fail) | assumption",
            "theorem t : True := by generalize (x = x) = P",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
        for tail in [
            "generalize",
            "generalize x",
            "generalize x =",
            "generalize = y",
            "generalize h : = y",
            "generalize x = _",
            "generalize x = y at h",
            "generalize x = y, z = w",
            "generalize x = y extra",
        ] {
            let source = format!("theorem t : True := by {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn malformed_refinement_never_drops_trailing_tokens() {
        for tail in [
            "constructor 1",
            "left h",
            "right h",
            "refine",
            "refine ?",
            "refine ? _",
            "refine ?7",
            "refine ?a.b",
            "refine ?/-gap-/_",
        ] {
            let source = format!("theorem t : 0 = 0 := by {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn deeply_grouped_synthetic_holes_use_heap_parser_frames() {
        std::thread::Builder::new()
            .name("deep-refinement-parser".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                let source = format!(
                    "theorem t : 0 = 0 := by refine {}?_{}; rfl",
                    "(".repeat(1000),
                    ")".repeat(1000)
                );
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn deeply_grouped_generalization_uses_a_small_stack() {
        std::thread::Builder::new()
            .name("deep-generalize-parser".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                for witness in ["", "h : "] {
                    let source = format!(
                        "theorem t : 0 = 0 := by generalize {witness}{}0{} = x; rfl",
                        "(".repeat(1000),
                        ")".repeat(1000),
                    );
                    let parsed = parse_definition(source.as_bytes()).unwrap();
                    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// `depth` proof blocks, each but the outermost inside its parent's `exact` term.
    fn nested_proofs(depth: usize) -> String {
        let mut body = String::from("rfl");
        for _ in 1..depth {
            body = format!("exact ⟨h, by {body}⟩");
        }
        format!("theorem t (h : 1 = 1) : 1 = 1 := by {body}\n")
    }

    // A debug build needs between 384 and 512 KiB here for the refused level.
    #[test]
    fn proofs_nested_in_tactic_terms_stop_at_the_limit_on_a_small_stack() {
        std::thread::Builder::new()
            .name("nested-proof-parser".to_string())
            .stack_size(1024 * 1024)
            .spawn(|| {
                let deepest = nested_proofs(PROOF_NESTING);
                let parsed = parse_definition(deepest.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), deepest.as_bytes());
                let refused = nested_proofs(PROOF_NESTING + 1);
                let innermost = BytePos(refused.rfind("by").unwrap());
                assert!(matches!(
                    parse_definition(refused.as_bytes()),
                    Err(NatDefinitionParseError::OutsideSeedGrammar {
                        at,
                        expected: NatDefinitionExpectation::Tactic,
                    }) if at == innermost
                ));
                // The refusal closed every block it had opened.
                assert!(parse_definition(deepest.as_bytes()).is_ok());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod simpa_tests {
    use super::*;
    #[test]
    fn completion_preserves_using_terms_comments_and_scoped_identifiers() {
        for tail in [
            "simpa",
            "simpa only",
            "simpa only []",
            "simpa using p",
            "simpa only [h, *] using (f p)",
            // `using` is a keyword at the pin, so a lemma named `using` is escaped.
            "simpa [«using», -N.rule] /- 🦀 -/ using «using»",
            "simpa only [(N.rule.{u} x)] using p",
        ] {
            let source = format!("theorem t (P : Prop) (p : P) : P := by\r\n  {tail}\r\n");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        }
    }
    #[test]
    fn completion_does_not_ignore_bad_options_locations_or_missing_evidence() {
        for tail in [
            "simpa using",
            "simpa only [,h]",
            "simpa at h",
            "simpa [h] at h using p",
            "simpa (config := {})",
            "simpa only [← *]",
            "simpa using (p",
            // `at` is a keyword at the pin, so the `using` term stops before it and the
            // Reference refuses the trailing `at h`; the hand table read `p at h` as one term.
            "simpa using p at h",
        ] {
            let source = format!("theorem t : True := by {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{tail}");
        }
        // `using` is a keyword at the pin: escaped it is an ordinary name, bare it is refused.
        assert!(parse_definition("def simpa («using» : Nat) := «using»".as_bytes()).is_ok());
        assert!(parse_definition(b"def simpa (using : Nat) := using").is_err());
    }
    #[test]
    fn deeply_grouped_using_evidence_uses_the_bounded_heap_parser() {
        std::thread::Builder::new()
            .name("deeply_grouped_using_evidence_uses_the_bounded_heap_parser".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                let source = format!(
                    "theorem t (P : Prop) (p : P) : P := by simpa only [] using {}p{}",
                    "(".repeat(2000),
                    ")".repeat(2000)
                );
                let parsed = parse_definition(source.as_bytes()).unwrap();
                assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod search_tests {
    use super::*;

    #[test]
    fn solve_by_elim_is_contextual_lossless_and_composes_with_controls() {
        for source in [
            "def solve_by_elim (n : Nat) : Nat := n",
            "theorem t (p : Prop) (h : p) : p := by\r\n  solve_by_elim /- local search -/\r\n",
            "theorem t : P := by first | solve_by_elim | assumption",
            "theorem t : And P Q := by constructor <;> (solve_by_elim)",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
    }

    #[test]
    fn solve_by_elim_does_not_silently_ignore_unsupported_options() {
        for tail in [
            "solve_by_elim h",
            "solve_by_elim [h]",
            "solve_by_elim only",
            "solve_by_elim (config := {})",
            "solve_by_elim at h",
        ] {
            let source = format!("theorem t : True := by {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
}

#[cfg(test)]
mod simp_all_tests {
    use super::*;

    #[test]
    fn simp_all_has_its_own_lossless_syntax_and_is_contextual() {
        for tactic in [
            "simp_all",
            "simp_all only",
            "simp_all only [h, <- k,]",
            "simp_all [*, -N.rule]",
        ] {
            let source = format!("theorem t : True := by\r\n  /- 🦀 -/ {tactic}\r\n");
            let parsed = parse_source_command(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
            let mut pending = vec![parsed.syntax()];
            let mut count = 0;
            while let Some(syntax) = pending.pop() {
                if let Syntax::Node { kind, args, .. } = syntax {
                    if kind == &parser_kind(&["Tactic", "simpAll"]) {
                        assert_eq!(args.len(), 5);
                        assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "simp_all"));
                        count += 1;
                    }
                    pending.extend(args);
                }
            }
            assert_eq!(count, 1);
        }
        assert!(parse_definition(b"def simp_all (n : Nat) := n").is_ok());
    }

    #[test]
    fn unsupported_simp_all_arguments_do_not_disappear() {
        for tactic in [
            "simp_all at *",
            "simp_all only at h",
            "simp_all [] using h",
            "simp_all [h,,k]",
        ] {
            let source = format!("theorem t : True := by {tactic}");
            assert!(parse_source_command(source.as_bytes()).is_err(), "{source}");
        }
    }
}
