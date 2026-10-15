//! Selected-lemma grammars from the pinned Init/Tactics.lean.
//! Preserve each tactic's exact slots and every argument category; terms use
//! the ordinary bounded parser, never token-spelling lookup in the elaborator.
use super::*;

fn kind(name: &str) -> Name {
    parser_kind(&["Tactic", "SolveByElim", name])
}

fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|token| &token.kind), Some(TokenKind::Symbol(word)) if word == text)
}

#[inline(never)]
pub(super) fn parse(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let name = match &keyword {
        Syntax::Atom { val, .. } if val == "solve_by_elim" => "solveByElim",
        Syntax::Atom { val, .. } if val == "apply_assumption" => "applyAssumption",
        Syntax::Atom { val, .. } if val == "apply_rules" => "applyRules",
        _ => return Err(refusal(view, tokens, range.start)),
    };
    let solve = name == "solveByElim";
    let mut at = range.start + 1;
    let all_goals = if solve && at < range.end && symbol(tokens, at, "*") {
        let slot = null_node(vec![leaves.leaf(at)?]);
        at += 1;
        slot
    } else {
        null_node(Vec::new())
    };
    let (config, after_config) = config(leaves, view, tokens, at, range.end)?;
    at = after_config;
    let only = if at < range.end
        && matches!(&tokens[at].kind, TokenKind::Ident(name) if *name == Name::from_components(["only"]))
    {
        let slot = null_node(vec![Syntax::Atom {
            info: leaves.leaf(at)?.info(),
            val: "only".into(),
        }]);
        at += 1;
        slot
    } else {
        null_node(Vec::new())
    };
    let arguments = if at < range.end && symbol(tokens, at, "[") {
        let close = rcases::closing(tokens, at)
            .filter(|&close| close < range.end && symbol(tokens, close, "]"))
            .ok_or_else(|| refusal(view, tokens, at))?;
        let mut rows = Vec::new();
        if close > at + 1 {
            for item in comma_separated(tokens, at + 1..close) {
                if item.is_empty() {
                    // sepBy allows a final comma, never a leading/doubled one.
                    if item.start == close && !rows.is_empty() {
                        break;
                    }
                    return Err(refusal(view, tokens, item.start));
                }
                let end = item.end;
                let argument = argument(leaves, view, tokens, item)?;
                rows.push(Syntax::node(kind("arg"), vec![argument]));
                if end < close {
                    rows.push(leaves.leaf(end)?);
                }
            }
        }
        let result = null_node(vec![Syntax::node(
            kind("args"),
            vec![leaves.leaf(at)?, null_node(rows), leaves.leaf(close)?],
        )]);
        at = close + 1;
        result
    } else {
        null_node(Vec::new())
    };
    // Label-attribute lookup is not implemented. Never accept and ignore a
    // `using` suffix (nor an arbitrary trailing token).
    if at != range.end {
        return Err(refusal(view, tokens, at));
    }
    let mut slots = vec![keyword];
    if solve {
        slots.push(all_goals);
    }
    slots.extend([config, only, arguments, null_node(Vec::new())]);
    Ok(Syntax::node(parser_kind(&["Tactic", name]), slots))
}

fn argument(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    item: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if symbol(tokens, item.start, "*") {
        if item.len() != 1 {
            return Err(refusal(view, tokens, item.start + 1));
        }
        return Ok(Syntax::node(kind("star"), vec![leaves.leaf(item.start)?]));
    }
    let erase = symbol(tokens, item.start, "-");
    let first = item.start + usize::from(erase);
    if first >= item.end {
        return Err(refusal(view, tokens, item.end));
    }
    if erase {
        // The pin's erase takes term:max, not an unparenthesized application.
        let end = match &tokens[first].kind {
            TokenKind::Ident(_) => first + 1,
            TokenKind::Symbol(word) if crate::canonical_bracket(word) == "(" => {
                rcases::closing(tokens, first)
                    .map(|close| close + 1)
                    .ok_or_else(|| refusal(view, tokens, first))?
            }
            _ => return Err(refusal(view, tokens, first)),
        };
        if end != item.end {
            return Err(refusal(view, tokens, end));
        }
    }
    let term = bounded_term(
        leaves,
        view,
        tokens,
        first..item.end,
        DefinitionGrammar::Scalar,
    )?;
    Ok(if erase {
        Syntax::node(kind("erase"), vec![leaves.leaf(item.start)?, term])
    } else {
        term
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(source: &str) -> Result<Syntax, NatDefinitionParseError> {
        let original = SourceText::from_utf8(source.as_bytes()).unwrap();
        let view = SourceView::of(&original);
        let tokens = command_scope::tokens(&view).unwrap();
        let leaves = Leaves::build(view.normalized(), &tokens).unwrap();
        let word = match &tokens[0].kind {
            TokenKind::Ident(word) => word.to_display_string(),
            TokenKind::Symbol(word) => word.clone(),
            _ => panic!("tactic keyword"),
        };
        let keyword = Syntax::atom(leaves.leaf(0).unwrap().info(), word);
        let syntax = parse(&leaves, &view, &tokens, 0..tokens.len(), keyword)?;
        assert_eq!(
            syntax
                .reconstruct(view.normalized(), leaves.attachment().epilogue())
                .unwrap(),
            source.replace("\r\n", "\n").as_bytes(),
        );
        Ok(syntax)
    }

    #[test]
    fn greedy_rule_categories_keep_five_slots_and_every_config_or_argument_leaf() {
        for (word, name) in [
            ("apply_rules", "applyRules"),
            ("apply_assumption", "applyAssumption"),
        ] {
            for suffix in [
                "",
                " only []",
                " only [*]",
                " [-h, h]",
                " (maxDepth := (0x10)) -symm +exfalso only [*, -h, (f h),]",
                " (symm := false) (exfalso := Bool.true) [f h]",
                " /- λ 🦀 -/\r\n only [«x.y», h₂,]",
            ] {
                let syntax = read(&format!("{word}{suffix}")).unwrap();
                let Syntax::Node { kind, args, .. } = &syntax else {
                    panic!("node")
                };
                assert_eq!(kind, &parser_kind(&["Tactic", name]));
                assert_eq!(args.len(), 5);
                assert_eq!(args[1].kind(), Some(&parser_kind(&["Tactic", "optConfig"])));
                assert!(matches!(&args[4], Syntax::Node {args, ..} if args.is_empty()));
            }
        }
    }

    #[test]
    fn greedy_rules_refuse_stars_missing_arguments_and_unimplemented_label_sets() {
        for word in ["apply_rules", "apply_assumption"] {
            for suffix in [
                "*",
                " [",
                " [h,,h]",
                " [,h]",
                " [-]",
                " [* h]",
                " [-f h]",
                " using other",
                " [h] trailing",
                " (maxDepth :=)",
                "+",
                " (symm := true",
            ] {
                let source = format!("{word}{suffix}");
                assert!(read(&source).is_err(), "{source}");
            }
        }
    }

    #[test]
    fn solve_search_keeps_its_separate_star_slot_and_configuration_tree() {
        for source in [
            "solve_by_elim",
            "solve_by_elim* only [*]",
            "solve_by_elim [-h, h]",
            "solve_by_elim (maxDepth := 12)",
            "solve_by_elim* -intro +constructor only [*]",
        ] {
            assert!(matches!(&read(source).unwrap(), Syntax::Node {args, ..} if args.len() == 6));
        }
        assert!(read("solve_by_elim (maxDepth :=)").is_err());
    }
}
