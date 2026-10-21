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
    kind: &'a Name,
    suffix: &'a str,
}

/// A sole suffix capture binds the whole sequence. Mixed template parts are
/// constructed separately; bracketed `$[...]*` has no native interpreter yet.
pub(in super::super) fn whole(syntax: &Syntax) -> Result<Option<Sequence<'_>>, &'static str> {
    let Some([suffix_node]) = null_args(syntax) else {
        return Ok(None);
    };
    suffix(suffix_node)
}

/// Interpret only direct children of a repetition's null node as splices.
pub(super) fn suffix(suffix_node: &Syntax) -> Result<Option<Sequence<'_>>, &'static str> {
    let Syntax::Node { kind, args, .. } = suffix_node else {
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
        kind,
        suffix,
    }))
}

pub(super) struct Tail<'a> {
    pub(super) prefix: &'a [Syntax],
    pub(super) sequence: Sequence<'a>,
}

/// A fixed prefix followed by one array capture. All prefix
/// captures retain ordinary paths; only the tail's path denotes a slice.
/// This is the pin's `slice prefix 0` match, not backtracking over partitions.
pub(super) fn tail(syntax: &Syntax) -> Result<Option<Tail<'_>>, &'static str> {
    let Some(items) = null_args(syntax) else {
        return Ok(None);
    };
    if items.len() < 2 {
        return Ok(None);
    }
    let Some((suffix, prefix)) = items.split_last() else {
        return Ok(None);
    };
    let Some(sequence) = self::suffix(suffix)? else {
        return Ok(None);
    };
    let parent = sequence.kind.parent();
    if parent == Name::from_components(["sepBy"]) {
        // The separator preceding the slice belongs to the fixed prefix.
        // It is not an element of the TSepArray bound to the tail. An even
        // prefix length preserves element/separator parity after projection.
        let separator = &sequence.suffix[..sequence.suffix.len() - 1];
        if prefix.len() % 2 != 0
            || prefix
                .iter()
                .skip(1)
                .step_by(2)
                .any(|item| !matches!(item, Syntax::Atom { val, .. } if val == separator))
        {
            return Err("a separated repetition tail with malformed prefix framing");
        }
    } else if parent != Name::from_components(["many"]) {
        return Ok(None);
    }
    if prefix.iter().any(|p| {
        p.kind()
            .is_some_and(|k| k.leaf_view() == LeafView::Str("antiquot_suffix_splice"))
    }) {
        return Err("multiple repetition captures in one pattern sequence");
    }
    Ok(Some(Tail { prefix, sequence }))
}

/// Extract only after matching established the prefix. Keep the captured
/// leaves (including source locations and hygiene) verbatim. Do not encode
/// from-the-end indices into the journal's ordinary child paths.
pub(in super::super) fn project<'a>(
    pattern: Option<&Syntax>,
    value: &'a Syntax,
) -> Result<std::borrow::Cow<'a, Syntax>, &'static str> {
    if let Some(pattern) = pattern
        && let Some(tail) = tail(pattern)?
    {
        let items = null_args(value).ok_or("a repetition tail outside its sequence")?;
        let suffix = items
            .get(tail.prefix.len()..)
            .ok_or("a repetition tail without its prefix")?;
        return Ok(std::borrow::Cow::Owned(null_node(suffix.to_vec())));
    }
    Ok(std::borrow::Cow::Borrowed(value))
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
    /// alone, and instantiation appends the capture at this sequence slot.
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
        Ok(Syntax::Node {
            info: *info,
            kind: kind.clone(),
            args: vec![capture, args[1].clone()],
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
        let rebound = null_node(vec![captured.template().unwrap()]);
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

    #[test]
    fn tail_projection_keeps_prefix_paths_separate_and_never_includes_the_head() {
        let head = Name::from_components(["head"]);
        let rest = Name::from_components(["rest"]);
        let suffix = sequence("many", "*", synthetic_ident(rest.clone()));
        let head_sequence = sequence("many", "*", synthetic_ident(head.clone()));
        let head_capture = node_args(&null_args(&head_sequence).unwrap()[0]).unwrap()[0].clone();
        let pattern = null_node(vec![
            head_capture.clone(),
            null_args(&suffix).unwrap()[0].clone(),
        ]);
        assert_eq!(
            variables(std::slice::from_ref(&pattern)).unwrap(),
            vec![
                (vec![0], macro_variable(&rest)),
                (vec![0, 0], macro_variable(&head)),
            ]
        );
        let head_value = synthetic_ident(Name::from_components(["first"]));
        let tail_value = synthetic_ident(Name::from_components(["remaining"]));
        let value = null_node(vec![head_value.clone(), tail_value.clone()]);
        let projected = project(Some(&pattern), &value).unwrap();
        assert_eq!(null_args(&projected).unwrap(), &[tail_value]);
        assert!(matches!(
            project(Some(&head_capture), &head_value).unwrap(),
            std::borrow::Cow::Borrowed(_)
        ));
        assert_eq!(
            project(Some(&pattern), &null_node(vec![head_value]))
                .unwrap()
                .as_ref(),
            &null_node(vec![])
        );
        assert!(project(Some(&pattern), &null_node(vec![])).is_err());
        assert!(project(Some(&pattern), &Syntax::Missing).is_err());
    }

    #[test]
    fn ambiguous_tail_partitions_and_duplicate_variables_remain_refusals() {
        let name = Name::from_components(["xs"]);
        let suffix = sequence("many", "*", synthetic_ident(name.clone()));
        let splice = null_args(&suffix).unwrap()[0].clone();
        assert!(variables(&[null_node(vec![splice.clone(), splice.clone()])]).is_err());
        let head = node_args(&splice).unwrap()[0].clone();
        assert!(variables(&[null_node(vec![head, splice.clone()])]).is_err());
        assert!(variables(&[null_node(vec![splice, Syntax::Missing])]).is_err());
    }

    #[test]
    fn separated_tail_projection_consumes_the_prefix_separator_not_a_tail_element() {
        let suffix = sequence(
            "sepBy",
            ",*",
            synthetic_ident(Name::from_components(["xs"])),
        );
        let pattern = null_node(vec![
            Syntax::Missing,
            Syntax::atom(SourceInfo::None, ","),
            null_args(&suffix).unwrap()[0].clone(),
        ]);
        let capture = tail(&pattern).unwrap().unwrap();
        assert_eq!(capture.prefix.len(), 2);
        let a = synthetic_ident(Name::from_components(["a"]));
        let b = synthetic_ident(Name::from_components(["b"]));
        let value = null_node(vec![
            Syntax::Missing,
            Syntax::atom(SourceInfo::None, ","),
            a.clone(),
            Syntax::atom(SourceInfo::None, ","),
            b.clone(),
        ]);
        assert!(capture.sequence.accepts(&value, &mut 0).unwrap());
        assert_eq!(
            project(Some(&pattern), &value).unwrap().as_ref(),
            &null_node(vec![a, Syntax::atom(SourceInfo::None, ","), b])
        );
        let prefix_only = null_node(vec![Syntax::Missing, Syntax::atom(SourceInfo::None, ",")]);
        assert_eq!(
            project(Some(&pattern), &prefix_only).unwrap().as_ref(),
            &null_node(vec![])
        );
        assert!(project(Some(&pattern), &null_node(vec![Syntax::Missing])).is_err());
    }

    #[test]
    fn separated_tail_patterns_cannot_change_separator_or_element_parity() {
        let suffix = sequence(
            "sepBy",
            ",*",
            synthetic_ident(Name::from_components(["xs"])),
        );
        let splice = null_args(&suffix).unwrap()[0].clone();
        for pattern in [
            null_node(vec![Syntax::Missing, splice.clone()]),
            null_node(vec![
                Syntax::Missing,
                Syntax::atom(SourceInfo::None, ";"),
                splice,
            ]),
        ] {
            assert!(tail(&pattern).is_err());
            assert!(variables(&[pattern]).is_err());
        }
    }
}
