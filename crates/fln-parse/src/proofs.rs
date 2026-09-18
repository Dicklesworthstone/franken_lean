//! Bounded native proof scripts, preserving real token leaves and separators.
//!
//! Tactic arguments use the ordinary term driver. Local declarations own their
//! nested `by` blocks through the heap sequence planner; they never recursively
//! call this parser on source-controlled nesting depth. Other nested proof-term
//! positions remain outside the bounded grammar.

use super::*;
use std::ops::Range;
mod elimination;
pub(super) use elimination::calculation;
mod locations;

fn refusal(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::Tactic,
    }
}

pub(super) fn parse(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    by: usize,
    limit: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    let mut depth = 0_usize;
    let mut forall_commas = 0_usize;
    let mut end = by + 1;
    while end < limit {
        match &tokens[end].kind {
            TokenKind::Symbol(symbol)
                if matches!(symbol.as_str(), "(" | "[" | "{" | ".{" | "⦃") =>
            {
                depth += 1
            }
            TokenKind::Symbol(symbol) if matches!(symbol.as_str(), ")" | "]" | "}" | "⦄") => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            TokenKind::Symbol(symbol)
                if matches!(symbol.as_str(), "forall" | "∀") && depth == 0 =>
            {
                forall_commas += 1
            }
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
        return Err(refusal(view, tokens, first));
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
    // Nested proof blocks are owned by the heap-planned local-declaration
    // production. Other tactic arguments must not recursively reenter parse.
    if let Some(at) = range
        .clone()
        .find(|&at| matches!(&tokens[at].kind, TokenKind::Symbol(s) if s == "by"))
    {
        return Err(refusal(view, tokens, at));
    }
    let keyword = match &tokens[start].kind {
        TokenKind::Ident(name) => [
            "intro",
            "revert",
            "generalize",
            "exact",
            "assumption",
            "apply",
            "refine",
            "constructor",
            "left",
            "right",
            "rfl",
            "rw",
            "rewrite",
            "simp",
            "subst",
            "injection",
            "contradiction",
            "by_cases",
            "decide",
            "skip",
            "fail",
        ]
        .into_iter()
        .find(|word| name == &Name::from_components([*word]))
        .ok_or_else(|| refusal(view, tokens, start))?,
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
        "simp" => simplify(leaves, view, tokens, range, atom),
        "rw" | "rewrite" => rewrite(leaves, view, tokens, range, atom, keyword == "rw"),
        "generalize" => generalize(leaves, view, tokens, range, atom),
        "by_cases" => by_cases(leaves, view, tokens, range, atom),
        "exact" | "apply" | "refine" => term_tactic(leaves, view, tokens, range, keyword, atom),
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
        "intro" => {
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
            if range.end == start + 2 && matches!(&tokens[start + 1].kind, TokenKind::Ident(_)) =>
        {
            args.push(leaves.leaf(start + 1)?);
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
        "assumption" | "rfl" | "contradiction" | "constructor" | "left" | "right" | "skip"
        | "fail" | "decide"
            if range.end == start + 1 => {}
        _ => return Err(refusal(view, tokens, start)),
    }
    Ok(Syntax::node(parser_kind(&["Tactic", keyword]), args))
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
    Ok(Syntax::node(
        parser_kind(&["Tactic", "by_cases"]),
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
    close: bool,
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
    Ok(Syntax::node(
        parser_kind(&["Tactic", if close { "rwSeq" } else { "rewriteSeq" }]),
        vec![keyword, null_node(Vec::new()), rules, location],
    ))
}

/// Simplification with either an explicit-only set or the environment's native
/// simp registry. The optional `only` leaf remains visible in the syntax tree.
fn simplify(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let (range, location) = locations::split(leaves, view, tokens, range)?;
    let at = range.start + 1;
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
                let rule = if is(start, "-") {
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
        parser_kind(&["Tactic", "simp"]),
        vec![
            keyword,
            null_node(Vec::new()),
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
    fn unsupported_simp_features_are_not_silently_ignored() {
        for tail in [
            "subst",
            "simp only [h] at",
            "simp only [*]",
            "simp only [,h]",
            "simp only [h,,k]",
            "simp only [<-]",
            "simp only [h] garbage",
            "simp only [by rfl]",
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
            "def have (n : Nat) : Nat := n",
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
            "have h := (by rfl)",
            "have h : 0 = 0 := by\n  exact h",
        ] {
            let source = format!("theorem t : 0 = 0 := by\n  {tail}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn nested_local_proofs_use_heap_frames() {
        std::thread::Builder::new()
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
}
