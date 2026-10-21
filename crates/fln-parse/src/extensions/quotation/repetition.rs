//! Whole repetition captures, not iteration of an arbitrary MacroM expression.
//!
//! The pinned Quotation.getHeadInfo binds a sole suffix splice unconditionally
//! as an Option, TSyntaxArray or TSepArray. In particular, the annotation on
//! `$xs:num,*` is NOT a per-element pattern test. Keep the original null node
//! (including separator source information) as the captured sequence.
use super::*;

#[cfg(test)]
mod slice_tests;

pub(in super::super) struct Sequence<'a> {
    capture: &'a Syntax,
    suffix_node: &'a Syntax,
    kind: &'a Name,
    suffix: &'a str,
    elementwise: bool,
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
    let leaf = kind.leaf_view();
    let (capture, suffix, elementwise) = match leaf {
        LeafView::Str("antiquot_suffix_splice") => {
            let [capture, Syntax::Atom { val: suffix, .. }] = args.as_slice() else {
                return Err("a malformed repetition suffix splice");
            };
            (capture, suffix.as_str(), false)
        }
        LeafView::Str("antiquot_scope") => {
            let [body, Syntax::Atom { val: suffix, .. }] = args.as_slice() else {
                return Err("a malformed bracketed repetition splice");
            };
            let Some([capture]) = null_args(body) else {
                return Err(
                    "a bracketed repetition body outside the supported single-capture subset",
                );
            };
            if antiquotation_name(capture).is_none() {
                return Err("a bracketed repetition body without a direct capture");
            }
            (capture, suffix.as_str(), true)
        }
        _ => return Ok(None),
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
        elementwise,
    }))
}

pub(super) struct Slice<'a> {
    pub(super) prefix: &'a [Syntax],
    pub(super) fixed_suffix: &'a [Syntax],
    pub(super) sequence: Sequence<'a>,
}

/// One array capture between fixed prefix/suffix syntax. The pin's `slice p s`
/// rule fixes both ends without trying partitions. Stored capture paths still
/// describe the pattern; `resolve` translates suffix paths against each value.
pub(super) fn slice(syntax: &Syntax) -> Result<Option<Slice<'_>>, &'static str> {
    let Some(items) = null_args(syntax) else {
        return Ok(None);
    };
    if items.len() < 2 {
        return Ok(None);
    }
    let mut found = None;
    for (index, item) in items.iter().enumerate() {
        if let Some(sequence) = suffix(item)? {
            if found.is_some() {
                return Err("multiple repetition captures in one pattern sequence");
            }
            found = Some((index, sequence));
        }
    }
    let Some((index, sequence)) = found else {
        return Ok(None);
    };
    let prefix = &items[..index];
    let fixed_suffix = &items[index + 1..];
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
        if fixed_suffix
            .iter()
            .step_by(2)
            .any(|item| !matches!(item, Syntax::Atom { val, .. } if val == separator))
        {
            return Err("a separated repetition slice with malformed suffix framing");
        }
    } else if parent != Name::from_components(["many"]) {
        return Err("an optional capture mixed with fixed pattern syntax");
    }
    Ok(Some(Slice {
        prefix,
        fixed_suffix,
        sequence,
    }))
}

impl Slice<'_> {
    fn range(&self, len: usize) -> Option<std::ops::Range<usize>> {
        let end = len.checked_sub(self.fixed_suffix.len())?;
        (end >= self.prefix.len()).then_some(self.prefix.len()..end)
    }
}

/// Resolve a structural pattern path, translating every suffix offset against
/// the corresponding matched value. This also covers nested patterns inside a
/// suffix and keeps serialized paths independent of the number of arguments.
pub(super) fn resolve<'a>(
    pattern: Option<&Syntax>,
    args: &'a [Syntax],
    path: &[usize],
    visited: &mut usize,
) -> Result<std::borrow::Cow<'a, Syntax>, &'static str> {
    if path.len() > MAX_DESCR_DEPTH {
        return Err("a capture path past the depth budget");
    }
    templates::charge(visited)?;
    let (first, rest) = path.split_first().ok_or("an empty capture path")?;
    let mut value = args.get(*first).ok_or("a capture without its operand")?;
    let mut pattern = match pattern {
        Some(p) => Some(
            node_args(p)
                .and_then(|p| p.get(*first))
                .ok_or("a capture outside its pattern")?,
        ),
        None => None,
    };
    for index in rest {
        templates::charge(visited)?;
        let value_args = node_args(value).ok_or("a capture through a syntax leaf")?;
        let mut actual = *index;
        if let Some(p) = pattern {
            // Scanning the same pattern for several suffix captures is real
            // work too. Charge it before allocating a projected capture.
            for _ in node_args(p).unwrap_or(&[]) {
                templates::charge(visited)?;
            }
            if let Some(slice) = slice(p)? {
                let range = slice
                    .range(value_args.len())
                    .ok_or("a capture without fixed ends")?;
                if *index == slice.prefix.len() {
                    return Err("a capture path into a repetition marker");
                }
                if *index > slice.prefix.len() {
                    let offset = *index - slice.prefix.len() - 1;
                    if offset >= slice.fixed_suffix.len() {
                        return Err("a capture beyond its pattern suffix");
                    }
                    actual = range.end + offset;
                }
            }
        }
        value = value_args
            .get(actual)
            .ok_or("a capture without its matched child")?;
        pattern = match pattern {
            Some(p) => Some(
                node_args(p)
                    .and_then(|p| p.get(*index))
                    .ok_or("a capture outside its pattern")?,
            ),
            None => None,
        };
    }
    project_metered(pattern, value, visited)
}

/// Match first, then extract the exact middle, including original source
/// leaves and hygiene. Account for projected subtrees before copying them.
fn project_metered<'a>(
    pattern: Option<&Syntax>,
    value: &'a Syntax,
    visited: &mut usize,
) -> Result<std::borrow::Cow<'a, Syntax>, &'static str> {
    if let Some(pattern) = pattern {
        for _ in node_args(pattern).unwrap_or(&[]) {
            templates::charge(visited)?;
        }
    }
    if let Some(pattern) = pattern
        && let Some(slice) = slice(pattern)?
    {
        let items = null_args(value).ok_or("a repetition slice outside its sequence")?;
        let range = slice
            .range(items.len())
            .ok_or("a repetition slice without its fixed ends")?;
        templates::charge(visited)?;
        let captured = items[range]
            .iter()
            .map(|item| templates::copy_capture(item, visited))
            .collect::<Result<Vec<_>, _>>()?;
        return Ok(std::borrow::Cow::Owned(null_node(captured)));
    }
    Ok(std::borrow::Cow::Borrowed(value))
}

#[cfg(test)]
fn project<'a>(
    pattern: Option<&Syntax>,
    value: &'a Syntax,
) -> Result<std::borrow::Cow<'a, Syntax>, &'static str> {
    project_metered(pattern, value, &mut 0)
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
        let kind = if self.elementwise {
            Name::str(kind.parent(), "antiquot_suffix_splice")
        } else {
            kind.clone()
        };
        Ok(Syntax::Node {
            info: *info,
            kind,
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
        if self.elementwise {
            let values: Box<dyn Iterator<Item = &Syntax> + '_> =
                if parent == Name::from_components(["sepBy"]) {
                    Box::new(items.iter().step_by(2))
                } else {
                    Box::new(items.iter())
                };
            for value in values {
                templates::charge(visited)?;
                if !super::capture_kind_matches(self.capture, value)? {
                    return Ok(false);
                }
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
    fn fixed_suffixes_bind_but_ambiguous_partitions_and_duplicate_variables_refuse() {
        let name = Name::from_components(["xs"]);
        let suffix = sequence("many", "*", synthetic_ident(name.clone()));
        let splice = null_args(&suffix).unwrap()[0].clone();
        assert!(variables(&[null_node(vec![splice.clone(), splice.clone()])]).is_err());
        let head = node_args(&splice).unwrap()[0].clone();
        assert!(variables(&[null_node(vec![head, splice.clone()])]).is_err());
        assert!(variables(&[null_node(vec![splice, Syntax::Missing])]).is_ok());
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
        let capture = slice(&pattern).unwrap().unwrap();
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
            assert!(slice(&pattern).is_err());
            assert!(variables(&[pattern]).is_err());
        }
    }
}
