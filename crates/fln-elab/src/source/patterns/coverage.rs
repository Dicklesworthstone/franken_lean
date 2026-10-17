//! Constructor inventories and deferred missing cases in matrix fallbacks.
use super::*;

impl Context {
    /// A fallback is unreachable only when the heads are exactly the
    /// constructors of one admitted family, anchored by an explicit head.
    /// Relative siblings are checked against that family, not guessed from
    /// their spelling. This is a decision-tree fact, not a typing judgment:
    /// the ordinary match backend must still check every generated constructor
    /// branch against the actual discriminant.
    pub(super) fn matrix_constructors_exhaustive(
        &mut self,
        heads: &[usize],
        arena: &[Pattern<'_>],
        canonical: &HashMap<Head, Head>,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut family = None;
        for &pattern in heads {
            self.tick()?;
            let Pattern::Constructor(constructor) = &arena[pattern] else {
                return Ok(false);
            };
            let head = &canonical[&constructor.head];
            if head.relative {
                continue;
            }
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&head.name) else {
                return Ok(false);
            };
            family = Some(constructor.induct.clone());
            break;
        }
        let Some(family) = family else {
            // Without an explicit anchor, only the typed match backend knows
            // the family. An all-relative head set is not coverage evidence.
            return Ok(false);
        };
        let Some(ConstantInfo::Induct(inductive)) = self.txn.env.find(&family) else {
            return Ok(false);
        };
        // Bound the inventory copy by the already bounded source matrix. Do
        // not scan or copy an arbitrarily large family to decide a small match.
        if inductive.ctors.len() != heads.len() {
            return Ok(false);
        }
        let constructors = inductive.ctors.clone();
        let mut missing = HashSet::new();
        for constructor in constructors {
            self.tick()?;
            missing.insert(constructor);
        }
        for &pattern in heads {
            self.tick()?;
            let Pattern::Constructor(constructor) = &arena[pattern] else {
                return Ok(false);
            };
            let head = &canonical[&constructor.head];
            let name = if head.relative {
                family.append_core(&head.name)
            } else {
                head.name.clone()
            };
            if !missing.remove(&name) {
                return Ok(false);
            }
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(&name) else {
                return Ok(false);
            };
            if constructor.induct != family {
                return Ok(false);
            }
        }
        Ok(missing.is_empty())
    }
}

/// An empty generated match is deliberately a refusal, not an inhabitant or
/// a `nomatch` proof. `match_parts` rejects it with MissingConstructor whenever
/// the term driver reaches it. Retaining this obligation in the decision tree
/// lets the typed outer match discard only a genuinely unreachable constructor
/// fallback; untyped relative heads alone cannot decide that. Every original
/// source row still needs its ordinary matrixScope elaboration witness.
pub(super) fn missing_case(subject: Name) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "matchMatrix"]),
        vec![
            atom("match"),
            null(vec![]),
            null(vec![]),
            null(vec![Syntax::node(
                parser_kind(&["Term", "matchDiscr"]),
                vec![null(vec![]), identifier(subject)],
            )]),
            atom("with"),
            Syntax::node(parser_kind(&["Term", "matchAlts"]), vec![null(vec![])]),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_missing_case_is_an_unconditional_typed_refusal_not_a_term_hole() {
        let mut context = Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        );
        // Refuse before trying to give even the discriminant a type. This is
        // not a nomatch proof of emptiness and cannot inhabit an expected type.
        let missing = missing_case(Name::from_components(["not_in_scope"]));
        for expected in [None, Some(Expr::sort(Level::zero()))] {
            assert!(matches!(
                context.term(&missing, expected),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::Match(matching::MatchError::MissingConstructor)
                ))
            ));
            assert!(context.matrix_rows.is_empty());
        }
    }
}
