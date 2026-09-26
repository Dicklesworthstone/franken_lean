//! Explicit-else, single-element do branches reuse the term conditional plan.
//! Reclassify only statement positions, never terms inside actions or parentheses.
//! The owned heap walk retains every original leaf, including escaped identifiers.
use super::*;

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}
fn sequence(element: Syntax) -> Syntax {
    term("doSeqIndent", vec![null_node(vec![term(
        "doSeqItem", vec![element, null_node(vec![])],
    )])])
}
fn keyword(syntax: &Syntax, text: &str) -> bool {
    match syntax {
        Syntax::Atom { val, .. } => val == text,
        Syntax::Ident { val, raw_val, .. } => {
            val == &Name::from_components([text])
                && raw_val.end().0 - raw_val.start().0 == text.len()
        }
        _ => false,
    }
}
fn first_leaf(mut syntax: &Syntax) -> &Syntax {
    while let Syntax::Node { args, .. } = syntax {
        let Some(first) = args.first() else { break };
        syntax = first;
    }
    syntax
}

pub(super) fn element(
    syntax: Syntax,
    position: BytePos,
) -> Result<Syntax, NatDefinitionParseError> {
    let refusal = || NatDefinitionParseError::OutsideSeedGrammar {
        at: position,
        expected: NatDefinitionExpectation::ScalarValue,
    };
    if syntax.kind() != Some(&parser_kind(&["Term", "ifThenElse"])) {
        return Err(refusal());
    }
    enum Task {
        Visit(Syntax),
        Finish(Vec<Syntax>, Syntax),
    }
    let mut tasks = vec![Task::Visit(syntax)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Finish(mut header, otherwise) => {
                let no = values.pop().ok_or_else(refusal)?;
                let yes = values.pop().ok_or_else(refusal)?;
                header.push(sequence(yes));
                header.push(null_node(vec![]));
                header.push(null_node(vec![otherwise, sequence(no)]));
                values.push(term("doIf", header));
            }
            Task::Visit(mut syntax) => {
                if syntax.kind() == Some(&parser_kind(&["Term", "ifThenElse"])) {
                    let Syntax::Node { args, .. } = &mut syntax else { unreachable!() };
                    if args.len() != 7 {
                        return Err(refusal());
                    }
                    let mut args = std::mem::take(args);
                    let no = args.pop().expect("conditional else body");
                    let otherwise = args.pop().expect("conditional else token");
                    let yes = args.pop().expect("conditional then body");
                    let then = args.pop().expect("conditional then token");
                    let condition = args.pop().expect("conditional condition");
                    let binding = args.pop().expect("conditional binder");
                    let if_token = args.pop().expect("conditional if token");
                    if !keyword(&if_token, "if") || !keyword(&then, "then")
                        || !keyword(&otherwise, "else")
                    {
                        return Err(refusal());
                    }
                    tasks.push(Task::Finish(vec![if_token, term("doIfProp", vec![binding, condition]), then], otherwise));
                    tasks.push(Task::Visit(no));
                    tasks.push(Task::Visit(yes));
                } else if keyword(&syntax, "break") || keyword(&syntax, "continue") {
                    let stop = keyword(&syntax, "break");
                    let token = Syntax::atom(syntax.info(), if stop { "break" } else { "continue" });
                    values.push(term(if stop { "doBreak" } else { "doContinue" }, vec![token]));
                } else {
                    // Do not silently reinterpret unsupported control syntax as
                    // a call to a same-spelled user declaration. True nested do
                    // expressions retain their separate scope in the term tree.
                    let head = first_leaf(&syntax);
                    if ["break", "continue", "return", "for", "while", "repeat", "unless", "try"]
                        .iter().any(|word| keyword(head, word))
                    {
                        return Err(refusal());
                    }
                    values.push(term("doExpr", vec![syntax]));
                }
            }
        }
    }
    if values.len() != 1 {
        return Err(refusal());
    }
    values.pop().ok_or_else(refusal)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn count(syntax: &Syntax, label: &str) -> usize {
        let expected = parser_kind(&["Term", label]);
        let mut pending = vec![syntax];
        let mut found = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node {kind,args,..} = syntax {
                found += usize::from(kind == &expected);
                pending.extend(args);
            }
        }
        found
    }
    #[test]
    fn conditional_loop_jumps_and_action_branches_preserve_source() {
        for source in [
            "def run : Nat := do { for x in xs do { if x == 1 then continue else visit x; after x }; return 7 }",
            "def run : Nat := do\r\n  for «𝒙» in xs do\r\n    if flag then break else visit «𝒙»\r\n    after «𝒙»\r\n  return 7",
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(count(parsed.syntax(), "doIf"), 1);
            assert_eq!(count(parsed.syntax(), "doIfProp"), 1);
            assert_eq!(count(parsed.syntax(), "doBreak") + count(parsed.syntax(), "doContinue"), 1);
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(parsed.reconstruct_normalized().unwrap(), parsed.source_view().normalized().as_bytes());
        }
    }
    #[test]
    fn nested_statement_conditionals_do_not_reclassify_parenthesized_terms() {
        let source = "def run : Nat := do { if a then if b then break else continue else (if c then «break» else «continue»); return 7 }";
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(count(parsed.syntax(), "doIf"), 2);
        assert_eq!(count(parsed.syntax(), "ifThenElse"), 1);
        assert_eq!(count(parsed.syntax(), "doBreak"), 1);
        assert_eq!(count(parsed.syntax(), "doContinue"), 1);
    }
    #[test]
    fn unsupported_or_malformed_branch_control_is_not_an_ordinary_application() {
        for branch in ["break 1", "continue x", "return 7"] {
            let source = format!("def run : Nat := do {{ if flag then {branch} else action; return 7 }}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
        let missing_else = "def run : Nat := do { if flag then action; return 7 }";
        assert!(parse_definition(missing_else.as_bytes()).is_err());
    }
}
