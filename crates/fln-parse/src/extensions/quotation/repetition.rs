//! Whole repetition captures, not iteration of an arbitrary MacroM expression.
//!
//! The pinned Quotation.getHeadInfo binds a sole suffix splice unconditionally
//! as an Option, TSyntaxArray or TSepArray. In particular, the annotation on
//! `$xs:num,*` is NOT a per-element pattern test. Keep the original null node
//! (including separator source information) as the captured sequence.
use super::*;

pub(in super::super) struct Sequence<'a> {
    capture: &'a Syntax,
    suffix_node: &'a Syntax,
    outer: &'a Syntax,
    kind: &'a Name,
    suffix: &'a str,
}

/// Only a whole sequence is supported here. A literal prefix/suffix or a
/// bracketed `$[...]*` still reaches the ordinary explicit splice refusal.
pub(in super::super) fn whole(syntax: &Syntax) -> Result<Option<Sequence<'_>>, &'static str> {
    let Some([suffix_node @ Syntax::Node { kind, args, .. }]) = null_args(syntax) else {
        return Ok(None);
    };
    if kind.leaf_view() != LeafView::Str("antiquot_suffix_splice") {
        return Ok(None);
    }
    let [capture, Syntax::Atom { val: suffix, .. }] = args.as_slice() else {
        return Err("a malformed repetition suffix splice");
    };
    let parent = kind.parent();
    let valid = if parent == Name::from_components(["sepBy"]) {
        suffix
            .strip_suffix('*')
            .is_some_and(|separator| !separator.is_empty())
    } else if parent == Name::from_components(["many"]) {
        suffix == "*"
    } else {
        parent == Name::from_components(["optional"]) && suffix == "?"
    };
    if !valid {
        return Err("an unsupported repetition suffix splice");
    }
    Ok(Some(Sequence {
        capture,
        suffix_node,
        outer: syntax,
        kind,
        suffix,
    }))
}

impl Sequence<'_> {
    pub(in super::super) fn name(&self) -> Result<Name, &'static str> {
        if let Some(name) = antiquotation_name(self.capture) {
            return Ok(name);
        }
        // `$(xs)?` is necessary to separate the optional suffix from an
        // identifier ending in '?'. Do not execute other nested expressions.
        let Syntax::Node { kind, args, .. } = self.capture else {
            return Err("a repetition splice without an antiquotation");
        };
        let [_, escapes, nested, _] = args.as_slice() else {
            return Err("a malformed repetition capture");
        };
        if kind.leaf_view() != LeafView::Str("antiquot")
            || !null_args(escapes).is_some_and(<[Syntax]>::is_empty)
            || !kind_is(nested, &["antiquotNestedExpr"])
        {
            return Err("an unsupported repetition capture expression");
        }
        match node_args(nested) {
            Some([_, Syntax::Ident { val, .. }, _]) => Ok(val.clone()),
            _ => Err("an unsupported repetition capture expression"),
        }
    }

    /// Retain the pinned splice shape in the lossless template. Only its bound
    /// identifier changes. Pre-resolution can then leave the macro variable
    /// alone, and instantiation replaces the entire null node exactly once.
    pub(in super::super) fn template(&self) -> Result<Syntax, &'static str> {
        let variable = synthetic_ident(macro_variable(&self.name()?));
        let Syntax::Node { info, kind, args } = self.capture else {
            return Err("a repetition capture without syntax children");
        };
        let [dollar, escapes, _, annotation] = args.as_slice() else {
            return Err("a malformed repetition capture");
        };
        let capture = Syntax::Node {
            info: *info,
            kind: kind.clone(),
            args: vec![
                dollar.clone(),
                escapes.clone(),
                variable,
                annotation.clone(),
            ],
        };
        let Syntax::Node { info, kind, args } = self.suffix_node else {
            return Err("a repetition suffix without syntax children");
        };
        let suffix = Syntax::Node {
            info: *info,
            kind: kind.clone(),
            args: vec![capture, args[1].clone()],
        };
        let Syntax::Node { info, kind, .. } = self.outer else {
            return Err("a repetition capture outside its sequence");
        };
        Ok(Syntax::Node {
            info: *info,
            kind: kind.clone(),
            args: vec![suffix],
        })
    }

    /// Check sequence framing, not the captured elements' syntax kinds. The
    /// ordinary parser owns those. Charge even wildcard/empty captures and
    /// share the work counter across all captures in a match or expansion.
    pub(in super::super) fn accepts(
        &self,
        value: &Syntax,
        visited: &mut usize,
    ) -> Result<bool, &'static str> {
        let Some(items) = null_args(value) else {
            return Ok(false);
        };
        *visited = visited
            .checked_add(items.len() + 1)
            .ok_or("repetition work overflow")?;
        if *visited > MAX_TEMPLATE_NODES {
            return Err("quoted repetition past the node budget");
        }
        let parent = self.kind.parent();
        if parent == Name::from_components(["optional"]) && items.len() > 1 {
            return Ok(false);
        }
        if parent == Name::from_components(["sepBy"]) {
            let separator = &self.suffix[..self.suffix.len() - 1];
            if items
                .iter()
                .skip(1)
                .step_by(2)
                .any(|item| !matches!(item, Syntax::Atom { val, .. } if val == separator))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sequence(kind: &str, suffix: &str, variable: Syntax) -> Syntax {
        null_node(vec![Syntax::node(
            Name::from_components([kind, "antiquot_suffix_splice"]),
            vec![
                Syntax::node(
                    Name::from_components(["num", "antiquot"]),
                    vec![
                        Syntax::atom(SourceInfo::None, "$"),
                        null_node(vec![]),
                        variable,
                        null_node(vec![]),
                    ],
                ),
                Syntax::atom(SourceInfo::None, suffix),
            ],
        )])
    }

    #[test]
    fn framing_is_bounded_and_a_resource_stop_is_not_a_nonmatch() {
        let pattern = sequence("many", "*", synthetic_ident(Name::from_components(["xs"])));
        let capture = whole(&pattern).unwrap().unwrap();
        let value = null_node(vec![Syntax::Missing; MAX_TEMPLATE_NODES]);
        assert_eq!(
            capture.accepts(&value, &mut 0),
            Err("quoted repetition past the node budget")
        );
        let small = null_node(vec![Syntax::Missing]);
        let mut shared = MAX_TEMPLATE_NODES - 2;
        assert_eq!(capture.accepts(&small, &mut shared), Ok(true));
        assert_eq!(
            capture.accepts(&null_node(vec![]), &mut shared),
            Err("quoted repetition past the node budget")
        );
        let mut exhausted = usize::MAX;
        assert!(capture.accepts(&small, &mut exhausted).is_err());
    }

    #[test]
    fn optional_and_separated_sequences_preserve_their_actual_framing() {
        let name = synthetic_ident(Name::from_components(["xs"]));
        let opt = sequence("optional", "?", name.clone());
        assert!(
            !whole(&opt)
                .unwrap()
                .unwrap()
                .accepts(&null_node(vec![Syntax::Missing; 2]), &mut 0)
                .unwrap()
        );
        let sep = sequence("sepBy", ",*", name);
        let captured = whole(&sep).unwrap().unwrap();
        for trailing in [false, true] {
            let mut items = vec![
                Syntax::Missing,
                Syntax::atom(SourceInfo::None, ","),
                Syntax::Missing,
            ];
            if trailing {
                items.push(Syntax::atom(SourceInfo::None, ","));
            }
            assert!(captured.accepts(&null_node(items), &mut 0).unwrap());
        }
        assert!(
            !captured
                .accepts(
                    &null_node(vec![Syntax::Missing, Syntax::atom(SourceInfo::None, ";")]),
                    &mut 0
                )
                .unwrap()
        );
        assert!(!captured.accepts(&Syntax::Missing, &mut 0).unwrap());
    }

    #[test]
    fn expression_captures_are_only_plain_identifiers_and_rebinding_is_lossless() {
        let xs = Name::from_components(["xs"]);
        let plain = sequence(
            "optional",
            "?",
            Syntax::node(
                Name::from_components(["antiquotNestedExpr"]),
                vec![
                    Syntax::atom(SourceInfo::None, "("),
                    synthetic_ident(xs.clone()),
                    Syntax::atom(SourceInfo::None, ")"),
                ],
            ),
        );
        let captured = whole(&plain).unwrap().unwrap();
        assert_eq!(captured.name(), Ok(xs.clone()));
        let rebound = captured.template().unwrap();
        assert_eq!(
            whole(&rebound).unwrap().unwrap().name(),
            Ok(macro_variable(&xs))
        );
        let computation = sequence(
            "many",
            "*",
            Syntax::node(
                Name::from_components(["antiquotNestedExpr"]),
                vec![
                    Syntax::atom(SourceInfo::None, "("),
                    null_node(vec![synthetic_ident(xs)]),
                    Syntax::atom(SourceInfo::None, ")"),
                ],
            ),
        );
        assert!(whole(&computation).unwrap().unwrap().name().is_err());
        assert!(whole(&sequence("unknown", "*", Syntax::Missing)).is_err());
    }
}
