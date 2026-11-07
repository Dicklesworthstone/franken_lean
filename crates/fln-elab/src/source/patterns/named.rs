//! Named patterns bind their whole receiver without changing the decision.
//!
//! The pin's `Term.namedPattern` and `CollectPatternVars.collect` in
//! Lean/Elab/PatternVar.lean retain an atomic alias as well as the payload.
//! The payload still supplies constructor/literal decisions and every original
//! row still needs a typing witness. This bounded lane has no named equality
//! assumptions (`x@h:p`); those must not be silently discarded.
use super::*;

pub(in crate::source) fn parts(
    syntax: &Syntax,
) -> Result<Option<(Name, &Syntax)>, NatDefinitionElabError> {
    if syntax.kind() != Some(&parser_kind(&["Term", "namedPattern"])) {
        return Ok(None);
    }
    let args = expect_node(
        syntax,
        &parser_kind(&["Term", "namedPattern"]),
        4,
        "named pattern",
    )?;
    let name = matching::pattern_name(&args[0])?.ok_or_else(invalid)?;
    expect_atom(&args[1], "@", "named pattern separator")?;
    expect_empty_null(&args[2], "named pattern equality assumption")?;
    Ok(Some((name, &args[3])))
}

impl Context {
    /// Peel only the current column, including nested aliases. Record the
    /// original private receiver identity before constructor specialization or
    /// literal splitting. Generated branch bindings then use matrixAlias's
    /// checked local-let path, just like an ordinary catchall name. The alias
    /// never replaces the payload by a wildcard or by the discriminant's value.
    pub(super) fn bind_named_matrix_column(
        &mut self,
        matrix: &mut Matrix<'_>,
        subject: &Name,
        arena: &[Pattern<'_>],
    ) -> Result<(), NatDefinitionElabError> {
        for row in &mut matrix.rows {
            self.tick()?;
            let column = row.patterns.first_mut().ok_or_else(invalid)?;
            while let Pattern::Named { name, pattern } = &arena[*column] {
                self.tick()?;
                row.bindings.push((name.clone(), subject.clone()));
                *column = *pattern;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(&Environment::new(), Budget::for_stack_bytes(128 * 1024))
    }
    fn named(name: Syntax, assumption: Syntax, pattern: Syntax) -> Syntax {
        Syntax::node(
            parser_kind(&["Term", "namedPattern"]),
            vec![name, atom("@"), assumption, pattern],
        )
    }

    #[test]
    fn only_a_complete_atomic_alias_without_an_equality_annotation_is_admitted() {
        let x = identifier(Name::from_components(["x"]));
        let good = named(x.clone(), null(vec![]), wildcard());
        assert!(parts(&good).unwrap().is_some());
        assert!(parts(&wildcard()).unwrap().is_none());
        for bad in [
            named(wildcard(), null(vec![]), wildcard()),
            named(
                identifier(Name::from_components(["N", "x"])),
                null(vec![]),
                wildcard(),
            ),
            named(
                x.clone(),
                null(vec![identifier(Name::from_components(["h"])), atom(":")]),
                wildcard(),
            ),
            Syntax::node(
                parser_kind(&["Term", "namedPattern"]),
                vec![x.clone(), atom("?"), null(vec![]), wildcard()],
            ),
            Syntax::node(
                parser_kind(&["Term", "namedPattern"]),
                vec![x, atom("@"), wildcard()],
            ),
        ] {
            assert!(parts(&bad).is_err());
        }
    }

    #[test]
    fn nested_aliases_are_heap_planned_and_refer_to_one_private_receiver() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut syntax = wildcard();
                for n in 0..2048 {
                    syntax = named(
                        identifier(Name::from_components([format!("alias{n}").as_str()])),
                        null(vec![]),
                        syntax,
                    );
                }
                let mut context = context();
                let mut arena = vec![Pattern::Bind(None)];
                let root = context.matrix_pattern(&syntax, &mut arena).unwrap();
                assert_eq!(arena.len(), 2050);
                let body = wildcard();
                let subject = context.matrix_name().unwrap();
                let mut matrix = Matrix {
                    recursive_root: false,
                    subjects: vec![],
                    rows: vec![Row {
                        patterns: vec![root],
                        bindings: vec![],
                        body: &body,
                        witness: Name::anonymous(),
                    }],
                };
                context
                    .bind_named_matrix_column(&mut matrix, &subject, &arena)
                    .unwrap();
                assert!(matches!(
                    arena[matrix.rows[0].patterns[0]],
                    Pattern::Bind(None)
                ));
                let aliases = &matrix.rows[0].bindings;
                assert_eq!(aliases.len(), 2048);
                for (n, (name, receiver)) in aliases.iter().enumerate() {
                    assert_eq!(
                        *name,
                        Name::from_components([format!("alias{}", 2047 - n).as_str()])
                    );
                    assert_eq!(*receiver, subject);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn alias_decoding_and_column_peeling_remain_metered() {
        let mut syntax = wildcard();
        for n in 0..64 {
            syntax = named(
                identifier(Name::from_components([format!("a{n}").as_str()])),
                null(vec![]),
                syntax,
            );
        }
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 8;
        assert!(matches!(
            stopped.matrix_pattern(&syntax, &mut vec![]),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        let mut complete = context();
        let mut arena = Vec::new();
        let root = complete.matrix_pattern(&syntax, &mut arena).unwrap();
        let body = wildcard();
        let mut matrix = Matrix {
            recursive_root: false,
            subjects: vec![],
            rows: vec![Row {
                patterns: vec![root],
                bindings: vec![],
                body: &body,
                witness: Name::anonymous(),
            }],
        };
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 8;
        assert!(matches!(
            stopped.bind_named_matrix_column(&mut matrix, &Name::anonymous(), &arena),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(stopped.txn.env, complete.txn.env);
        assert_eq!(stopped.txn.lctx, complete.txn.lctx);
        assert_eq!(stopped.txn.mvars, complete.txn.mvars);
    }
}
