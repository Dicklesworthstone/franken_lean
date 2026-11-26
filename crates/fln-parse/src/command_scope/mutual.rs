//! Atomic source groups for native mutual declarations.
//!
//! The pin's Command.mutual encloses commands between `mutual` and `end`.
//! This door accepts one to eight uniformly inductive, theorem, ordinary,
//! partial or unsafe members. Mixed kinds and scope changes are never sequentialized.
//! Members use the ordinary declaration parser over their exact source bytes.
use super::*;

fn refusal(view: &SourceView, tokens: &[LexedToken], at: usize) -> DefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::MutualBlockEnd,
    }
}

fn unsupported_member_label(syntax: &Syntax) -> &'static str {
    let Syntax::Node { kind, args, .. } = syntax else {
        return "command";
    };
    if kind != &Name::from_components(["Lean", "Parser", "Command", "declaration"])
        || args.len() != 2
    {
        return "command";
    }
    let Some(body_kind) = args[1].kind() else {
        return "command";
    };
    if body_kind == &parser_kind(&["Command", "structure"]) {
        if let Syntax::Node {
            args: struct_args, ..
        } = &args[1]
            && struct_args
                .first()
                .and_then(Syntax::kind)
                .is_some_and(|k| k == &parser_kind(&["Command", "classTk"]))
        {
            return "class";
        }
        return "structure";
    }
    if body_kind == &parser_kind(&["Command", "axiom"]) {
        "axiom"
    } else if body_kind == &parser_kind(&["Command", "opaque"]) {
        "opaque"
    } else if body_kind == &parser_kind(&["Command", "instance"]) {
        "instance"
    } else if body_kind == &parser_kind(&["Command", "example"]) {
        "example"
    } else if body_kind == &parser_kind(&["Command", "inductive"]) {
        "inductive"
    } else if body_kind == &parser_kind(&["Command", "coinductive"]) {
        "coinductive"
    } else if body_kind == &parser_kind(&["Command", "definition"]) {
        "def"
    } else if body_kind == &parser_kind(&["Command", "abbrev"]) {
        "abbrev"
    } else if body_kind == &parser_kind(&["Command", "theorem"]) {
        "theorem"
    } else {
        "declaration"
    }
}
fn word(view: &SourceView, token: &LexedToken, text: &str) -> bool {
    // Escaped identifiers such as «end», and strings/comments containing end,
    // are not delimiters. Structural Name equality alone would lose that fact.
    view.normalized().span_str(token.extent) == Some(text)
}

/// Locate the closing token without parsing or publishing any member. Delimiter
/// validation prevents a malformed telescope from exposing a later declaration
/// as a separate command. No host recursion, including for hostile nesting.
pub(super) fn block_end(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<usize, DefinitionParseError> {
    let mut delimiters = Vec::new();
    for (index, token) in tokens.iter().enumerate().skip(start + 1) {
        if delimiters.is_empty() {
            if word(view, token, "end") {
                return Ok(index);
            }
            if word(view, token, "mutual") {
                return Err(refusal(view, tokens, index));
            }
        }
        if let TokenKind::Symbol(symbol) = &token.kind {
            match crate::canonical_bracket(symbol.as_str()) {
                "(" => delimiters.push(")"),
                "{" | ".{" => delimiters.push("}"),
                "[" | "@[" => delimiters.push("]"),
                "⦃" => delimiters.push("⦄"),
                "⟨" => delimiters.push("⟩"),
                ")" | "}" | "]" | "⦄" | "⟩"
                    if delimiters.pop() != Some(crate::canonical_bracket(symbol.as_str())) =>
                {
                    return Err(refusal(view, tokens, index));
                }
                _ => {}
            }
        }
    }
    Err(refusal(view, tokens, tokens.len()))
}

/// Recognize a complete group and return its untrusted member syntax. The
/// original group's offsets survive parser errors inside every member. None
/// means this is an ordinary command, not an empty or malformed mutual group.
pub fn parse(source: &[u8]) -> Result<Option<Vec<Syntax>>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    Ok(parse_with_offsets(source)?.map(|members| {
        members
            .into_iter()
            .map(|(offset, mut syntax)| {
                // The elaborator receives the whole group's source site. Keep
                // every member's syntax in that group's normalized coordinates.
                // parse_with_offsets intentionally exposes raw offsets instead.
                let offset = view
                    .from_original(offset)
                    .expect("a member starts at a byte retained in the source view");
                let span = |value: ByteSpan| {
                    ByteSpan::new(
                        BytePos(value.start().0 + offset.0),
                        BytePos(value.end().0 + offset.0),
                    )
                    .expect("a member span remains inside its source group")
                };
                let shift = |info: &mut SourceInfo| match info {
                    SourceInfo::Original {
                        leading,
                        pos,
                        trailing,
                        end_pos,
                    } => {
                        *leading = span(*leading);
                        *trailing = span(*trailing);
                        pos.0 += offset.0;
                        end_pos.0 += offset.0;
                    }
                    SourceInfo::Synthetic { pos, end_pos, .. } => {
                        pos.0 += offset.0;
                        end_pos.0 += offset.0;
                    }
                    SourceInfo::None => {}
                };
                let mut pending = vec![&mut syntax];
                while let Some(node) = pending.pop() {
                    match node {
                        Syntax::Node { info, args, .. } => {
                            shift(info);
                            pending.extend(args.iter_mut());
                        }
                        Syntax::Atom { info, .. } => shift(info),
                        Syntax::Ident { info, raw_val, .. } => {
                            shift(info);
                            if let Some(source) = raw_val.source_span() {
                                *raw_val = span(source).into();
                            }
                        }
                        Syntax::Missing => {}
                    }
                }
                syntax
            })
            .collect()
    }))
}

/// The byte offset in `source` of a `mutual` block's keyword, where the pin positions a
/// message about the whole block; `None` when `source` is not one.
pub fn keyword_offset(source: &[u8]) -> Option<BytePos> {
    let original = SourceText::from_utf8(source).ok()?;
    let view = SourceView::of(&original);
    let tokens = super::tokens(&view).ok()?;
    let first = tokens.first()?;
    word(&view, first, "mutual").then(|| view.to_original(first.extent.start()))
}

/// The complete command tree, including the original `mutual` and `end` atoms.
/// Read-only editor consumers need these leaves as well as the members passed
/// to the elaborator. All member positions share the group's normalized view.
pub fn tree(source: &[u8]) -> Result<Option<Syntax>, DefinitionParseError> {
    let Some(members) = parse(source)? else {
        return Ok(None);
    };
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let end = block_end(&view, &tokens, 0)?;
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    Ok(Some(Syntax::node(
        parser_kind(&["Command", "mutual"]),
        vec![leaves.leaf(0)?, null_node(members), leaves.leaf(end)?],
    )))
}

/// Read the members of a canonical expanded `Command.mutual` without reparsing
/// generated text. Apply the same size and member-family restrictions as
/// [`parse`]; no command sequence or scope control gains declaration authority.
/// The returned syntax is still untrusted and requires atomic elaboration and
/// kernel admission.
pub fn syntax_members(syntax: &Syntax) -> Option<&[Syntax]> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    if kind != &parser_kind(&["Command", "mutual"]) {
        return None;
    }
    let [
        Syntax::Atom { val: opening, .. },
        Syntax::Node {
            kind: members_kind,
            args: members,
            ..
        },
        Syntax::Atom { val: closing, .. },
    ] = args.as_slice()
    else {
        return None;
    };
    if opening != "mutual"
        || closing != "end"
        || members_kind != &Name::from_components(["null"])
        || members.is_empty()
        || members.len() > 8
    {
        return None;
    }
    let first = member_kind(&members[0])?;
    members
        .iter()
        .all(|member| member_kind(member) == Some(first))
        .then_some(members.as_slice())
}

/// [`parse`], with each member's byte offset in `source`: a member's own positions are
/// relative to its start, so this offset places them in the group.
pub fn parse_with_offsets(
    source: &[u8],
) -> Result<Option<Vec<(BytePos, Syntax)>>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = super::tokens(&view)?;
    if !tokens
        .first()
        .is_some_and(|token| word(&view, token, "mutual"))
    {
        return Ok(None);
    }
    let end = block_end(&view, &tokens, 0)?;
    if end + 1 != tokens.len() || end == 1 {
        return Err(refusal(&view, &tokens, end));
    }
    // Keep indentation, documentation and visibility in each original member.
    // The ordinary command partitioner also splits same-line inductive members;
    // a second keyword-only splitter would drop prefixes from later members.
    let start = view.to_original(tokens[0].extent.end());
    let stop = view.to_original(tokens[end].extent.start());
    let commands = super::partition(&source[start.0..stop.0])
        .map_err(|error| error.with_original_offset(start))?;
    if commands.is_empty() || commands.len() > 8 {
        return Err(refusal(&view, &tokens, end));
    }
    let mut members = Vec::new();
    let mut group_kind: Option<MemberKind> = None;
    for (offset, bytes) in commands {
        let member_at = BytePos(start.0 + offset.0);
        let parsed =
            parse_definition(bytes).map_err(|error| error.with_original_offset(member_at))?;
        let Some(kind) = member_kind(&parsed.syntax) else {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: member_at,
                expected: NatDefinitionExpectation::SupportedMutualMember(
                    unsupported_member_label(&parsed.syntax),
                ),
            });
        };
        if let Some(previous) = group_kind
            && previous != kind
        {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: member_at,
                expected: NatDefinitionExpectation::UniformMutualMembers {
                    first: previous.label(),
                    found: kind.label(),
                },
            });
        }
        group_kind = Some(kind);
        members.push((member_at, parsed.syntax));
    }
    Ok(Some(members))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum MemberKind {
    Inductive,
    PartialDefinition,
    UnsafeDefinition,
    OrdinaryDefinition,
    Theorem,
}

impl MemberKind {
    const fn label(self) -> &'static str {
        match self {
            Self::Inductive => "inductive",
            Self::PartialDefinition => "partial def",
            Self::UnsafeDefinition => "unsafe def",
            Self::OrdinaryDefinition => "def",
            Self::Theorem => "theorem",
        }
    }
}

/// This is only group classification. Preserve the complete declaration and
/// every modifier for the elaborator's visibility and effect checks.
fn member_kind(syntax: &Syntax) -> Option<MemberKind> {
    let Syntax::Node { kind, args, .. } = syntax else {
        return None;
    };
    if kind != &Name::from_components(["Lean", "Parser", "Command", "declaration"])
        || args.len() != 2
    {
        return None;
    }
    if args[1].kind() == Some(&parser_kind(&["Command", "inductive"]))
        || args[1].kind() == Some(&parser_kind(&["Command", "classInductive"]))
    {
        return Some(MemberKind::Inductive);
    }
    let kind = args[1].kind()?;
    let theorem = kind == &parser_kind(&["Command", "theorem"]);
    let ordinary = theorem
        || kind == &parser_kind(&["Command", "definition"])
        || kind == &parser_kind(&["Command", "abbrev"]);
    if !ordinary {
        return None;
    }
    let Syntax::Node { kind, args, .. } = &args[0] else {
        return None;
    };
    if kind != &Name::from_components(["Lean", "Parser", "Command", "declModifiers"])
        || args.len() != 7
    {
        return None;
    }
    let has_modifier = |slot: usize, modifier: &str| {
        matches!(&args[slot], Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["null"])
                && args.len() == 1
                && args[0].kind() == Some(&Name::from_components(["Lean", "Parser", "Command", modifier])))
    };
    // Keep both markers on a conflicting unsafe/partial declaration; the
    // elaborator, not this classifier, must reject its complete modifier set.
    if has_modifier(6, "partial") {
        Some(MemberKind::PartialDefinition)
    } else if has_modifier(5, "unsafe") {
        Some(MemberKind::UnsafeDefinition)
    } else if theorem {
        Some(MemberKind::Theorem)
    } else {
        Some(MemberKind::OrdinaryDefinition)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expanded_groups_preserve_supported_member_families_and_order() {
        for source in [
            "mutual\ndef first : Nat := second\ndef second : Nat := 42\nend",
            "mutual\ntheorem first : True := True.intro\ntheorem second : True := first\nend",
            "mutual\npartial def first : Nat := second\npartial def second : Nat := first\nend",
            "mutual\nunsafe def first : Nat := second\nunsafe def second : Nat := 42\nend",
            "mutual\ninductive First where | mk (next : Second)\ninductive Second where | nil\nend",
            "mutual\ndef only : Nat := 42\nend",
        ] {
            let syntax = tree(source.as_bytes()).unwrap().unwrap();
            let members = syntax_members(&syntax).unwrap();
            assert_eq!(members, parse(source.as_bytes()).unwrap().unwrap());
        }
    }

    #[test]
    fn expanded_groups_refuse_malformed_mixed_and_oversized_trees() {
        let declaration = parse_definition(b"def first : Nat := 42").unwrap().syntax;
        let theorem = parse_definition(b"theorem proof : True := True.intro")
            .unwrap()
            .syntax;
        let example = parse_source_command(b"example : Nat := 42")
            .unwrap()
            .syntax()
            .clone();
        let group = |members| {
            Syntax::node(
                parser_kind(&["Command", "mutual"]),
                vec![
                    Syntax::atom(SourceInfo::None, "mutual"),
                    null_node(members),
                    Syntax::atom(SourceInfo::None, "end"),
                ],
            )
        };
        let valid = group(vec![declaration.clone()]);
        let mut malformed_open = valid.clone();
        let Syntax::Node { args, .. } = &mut malformed_open else {
            unreachable!()
        };
        args[0] = Syntax::atom(SourceInfo::None, "namespace");
        let mut malformed_end = valid.clone();
        let Syntax::Node { args, .. } = &mut malformed_end else {
            unreachable!()
        };
        args[2] = Syntax::Missing;
        let mut malformed_members = valid.clone();
        let Syntax::Node { args, .. } = &mut malformed_members else {
            unreachable!()
        };
        args[1] = Syntax::node(Name::from_components(["choice"]), vec![declaration.clone()]);
        let mut extra_argument = valid.clone();
        let Syntax::Node { args, .. } = &mut extra_argument else {
            unreachable!()
        };
        args.push(Syntax::Missing);
        for invalid in [
            Syntax::Missing,
            null_node(vec![declaration.clone()]),
            group(vec![]),
            group(vec![declaration.clone(); 9]),
            group(vec![declaration.clone(), theorem]),
            group(vec![example]),
            group(vec![Syntax::node(
                parser_kind(&["Command", "namespace"]),
                vec![],
            )]),
            group(vec![valid]),
            malformed_open,
            malformed_end,
            malformed_members,
            extra_argument,
        ] {
            assert!(syntax_members(&invalid).is_none(), "{invalid:?}");
        }
    }

    #[test]
    fn partial_groups_preserve_indentation_trivia_and_lexical_boundaries() {
        let source = "-- 🦀\r\nnamespace N\r\nmutual\r\n  partial def a (n : Nat) : Nat := if n == 0 then 7 else b (n - 1)\r\n  /- partial def fake := end -/\r\n  partial def b (n : Nat) : Nat := a n\r\nend\r\ndef z : Nat := a 0\r\nend N\r\n";
        let pieces = super::super::partition(source.as_bytes()).unwrap();
        assert_eq!(pieces.len(), 4);
        assert_eq!(
            pieces
                .iter()
                .flat_map(|(_, bytes)| bytes.iter().copied())
                .collect::<Vec<_>>(),
            source.as_bytes()
        );
        let members = parse(pieces[1].1).unwrap().unwrap();
        assert_eq!(members.len(), 2);
        assert!(parse(pieces[2].1).unwrap().is_none());
        assert!(matches!(
            super::super::parse(pieces[3].1).unwrap(),
            Some(ScopeCommand::End(Some(_)))
        ));
    }

    #[test]
    fn partial_groups_do_not_hide_mixed_or_oversized_commands() {
        for source in [
            "mutual\npartial def a : Nat := 1\naxiom b : Nat\nend",
            "mutual\npartial def a : Nat := 1\nnamespace N\nend\nend",
            "mutual\npartial def a : Nat := 1\nmutual\npartial def b : Nat := 2\nend\nend",
            "mutual\npartial def a : Nat := 1\ndef b : Nat := 2\nend",
            "mutual\npartial def a : Nat := 1\nend N",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
        let source = format!(
            "mutual\n{}end",
            (0..9)
                .map(|i| format!("  partial def p{i} : Nat := {i}\n"))
                .collect::<String>()
        );
        assert!(parse(source.as_bytes()).is_err());
    }

    #[test]
    fn the_keyword_offset_is_the_original_mutual_token() {
        let source = "-- 🦀 mutual\r\n/- mutual -/ mutual\r\n  def a : Nat := 1\r\nend";
        assert_eq!(
            keyword_offset(source.as_bytes()),
            Some(BytePos(source.rfind("mutual\r\n").unwrap()))
        );
        assert_eq!(keyword_offset(b"def mutual : Nat := 1"), None);
        assert_eq!(keyword_offset(b"\xff"), None);
    }

    #[test]
    fn partial_member_diagnostics_retain_original_crlf_unicode_offsets() {
        let source = "-- 🦀\r\nmutual\r\n  partial def a (n : Nat) : Nat := n\r\n  partial def b : Nat := if true then )\r\nend";
        let error = parse(source.as_bytes()).unwrap_err();
        assert_eq!(
            error.primary_offset().unwrap().0,
            source.rfind(')').unwrap()
        );
    }

    #[test]
    fn member_syntax_positions_use_the_normalized_group_view() {
        let source = "-- π\r\nmutual\r\n  def first : Nat := panic! \"first\"\r\n  def second : Nat := panic! \"second\"\r\nend\r\n";
        let normalized = source.replace("\r\n", "\n");
        let members = parse(source.as_bytes()).unwrap().unwrap();
        let mut positions = Vec::new();
        for member in &members {
            let mut pending = vec![member];
            while let Some(node) = pending.pop() {
                match node {
                    Syntax::Node { args, .. } => pending.extend(args.iter().rev()),
                    Syntax::Atom { info, val } if val == "panic!" => {
                        positions.push(info.pos(false).unwrap().0);
                    }
                    _ => {}
                }
            }
        }
        assert_eq!(
            positions,
            normalized
                .match_indices("panic!")
                .map(|(at, _)| at)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn groups_keep_member_bytes_and_surrounding_scope_boundaries() {
        let source = "-- mutual fake\r\nnamespace Demo\r\nmutual\r\n  inductive Tree where | node (xs : Forest)\r\n  /- end -/ inductive Forest where | nil | cons (t : Tree)\r\nend\r\ndef t : Tree := Tree.node Forest.nil\r\nend Demo\r\n";
        let commands = super::super::partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 4);
        let mut combined = Vec::new();
        for (offset, command) in &commands {
            assert_eq!(offset.0, combined.len());
            combined.extend_from_slice(command);
        }
        assert_eq!(combined, source.as_bytes());
        assert_eq!(parse(commands[1].1).unwrap().unwrap().len(), 2);
        assert!(parse(commands[2].1).unwrap().is_none());
        assert!(matches!(
            super::super::parse(commands[3].1).unwrap(),
            Some(ScopeCommand::End(Some(_)))
        ));
    }

    #[test]
    fn escaped_delimiters_are_names_and_group_members_are_not_rewritten() {
        let source =
            b"mutual inductive A where | mk (x : B) inductive B where | \xc2\xabend\xc2\xbb end";
        let members = parse(source).unwrap().unwrap();
        assert_eq!(members.len(), 2);
        let single = parse(b"mutual inductive A where | mk end")
            .unwrap()
            .unwrap();
        assert_eq!(single.len(), 1);
    }

    #[test]
    fn class_inductive_members_preserve_the_generated_keyword_group() {
        let members = parse(b"mutual\nclass inductive C where | mk\nend")
            .unwrap()
            .unwrap();
        let [
            Syntax::Node {
                args: declaration, ..
            },
        ] = members.as_slice()
        else {
            panic!("one canonical declaration");
        };
        let Syntax::Node { kind, args, .. } = &declaration[1] else {
            panic!("a canonical class inductive command");
        };
        assert_eq!(kind, &parser_kind(&["Command", "classInductive"]));
        assert_eq!(args.len(), 6);
        let Syntax::Node { kind, args, .. } = &args[0] else {
            panic!("grouped class inductive keywords");
        };
        assert_eq!(kind, &Name::from_components(["group"]));
        assert!(
            matches!(args.as_slice(), [Syntax::Atom { val: first, .. }, Syntax::Atom { val: second, .. }]
            if first == "class" && second == "inductive")
        );
        // Semantic rejection of multi-member class blocks belongs to the
        // inductive elaborator, which receives every original member.
        assert_eq!(
            parse(b"mutual\nclass inductive C where | mk\ninductive D where | mk\nend")
                .unwrap()
                .unwrap()
                .len(),
            2
        );
    }

    #[test]
    fn malformed_or_unsupported_groups_never_become_partial_commands() {
        for source in [
            "mutual end",
            "mutual inductive A where | mk",
            "mutual inductive A where | mk (x : Nat] end",
            "mutual inductive A where | mk end A",
            "mutual def x : Nat := 1 theorem y : True := True.intro end",
            "mutual inductive A where | mk def x := 1 end",
            "mutual namespace N inductive A where | mk end end",
            "mutual inductive A where | mk mutual inductive B where end end",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
        let oversized = format!(
            "mutual {} end",
            (0..9)
                .map(|i| format!("inductive A{i} where | mk "))
                .collect::<String>()
        );
        assert!(parse(oversized.as_bytes()).is_err());
    }

    #[test]
    fn member_parse_errors_use_original_group_byte_offsets() {
        let source =
            "-- 🦀\r\nmutual\r\ninductive A where | mk\r\ninductive B where | bad (x : Nat]\r\nend";
        let error = parse(source.as_bytes()).unwrap_err();
        assert_eq!(error.primary_offset().unwrap().0, source.find(']').unwrap());
        let source =
            "mutual\r\ninductive A where | mk\r\ninductive B where | bad deriving , Nat\r\nend";
        let error = parse(source.as_bytes()).unwrap_err();
        assert_eq!(error.primary_offset().unwrap().0, source.find(',').unwrap());
    }

    #[test]
    fn unsupported_and_mixed_members_name_member_kind_not_inductive_constructor() {
        for (source, expected) in [
            (
                "mutual\nstructure S where\n  x : Nat\nend",
                NatDefinitionExpectation::SupportedMutualMember("structure"),
            ),
            (
                "mutual\nclass C where\n  x : Nat\nend",
                NatDefinitionExpectation::SupportedMutualMember("class"),
            ),
            (
                "mutual\naxiom a : Nat\nend",
                NatDefinitionExpectation::SupportedMutualMember("axiom"),
            ),
            (
                "mutual\ndef x : Nat := 1\ntheorem y : True := True.intro\nend",
                NatDefinitionExpectation::UniformMutualMembers {
                    first: "def",
                    found: "theorem",
                },
            ),
            (
                "mutual\ninductive A where | mk\ndef x : Nat := 1\nend",
                NatDefinitionExpectation::UniformMutualMembers {
                    first: "inductive",
                    found: "def",
                },
            ),
            ("mutual end", NatDefinitionExpectation::MutualBlockEnd),
        ] {
            let error = parse(source.as_bytes()).unwrap_err();
            assert!(
                matches!(
                    error,
                    NatDefinitionParseError::OutsideSeedGrammar { expected: got, .. }
                        if got == expected
                ),
                "{source} => {error}"
            );
            assert!(
                !error.to_string().contains("InductiveConstructor"),
                "{error}"
            );
        }
    }
}
