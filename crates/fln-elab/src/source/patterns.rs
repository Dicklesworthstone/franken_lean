//! Heap-planned pattern matrices lowered to the ordinary checked match backend.
//!
//! This layer never learns constructors by evaluating a discriminant. It splits
//! source rows in order, retains all discriminants in checked local bindings,
//! and leaves constructor typing, coverage and index equations to the existing
//! elaborator. Every original row has an elaboration witness: a redundant row
//! cannot hide an ill-typed body when a generated fallback is unnecessary.
use super::*;
use fln_env::constants::ConstantInfo;
use fln_syntax::source::{ByteSpan, SourceInfo};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

#[derive(Clone, PartialEq, Eq, Hash)]
struct Head {
    relative: bool,
    name: Name,
}
struct Constructor<'a> {
    head: Head,
    syntax: &'a Syntax,
    fields: Vec<usize>,
}
enum Pattern<'a> {
    Bind(Option<Name>),
    Constructor(Constructor<'a>),
}
#[derive(Clone)]
struct Row<'a> {
    patterns: Vec<usize>,
    bindings: Vec<(Name, Name)>,
    body: &'a Syntax,
    witness: Name,
}
struct Matrix<'a> {
    subjects: Vec<Name>,
    rows: Vec<Row<'a>>,
}
struct Alternative {
    pattern: Syntax,
}

fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}
fn atom(text: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, text)
}
fn identifier(name: Name) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default(),
        val: name,
        preresolved: Vec::new(),
    }
}
fn wildcard() -> Syntax {
    Syntax::node(parser_kind(&["Term", "hole"]), vec![atom("_")])
}
fn bind(name: Name, value: Syntax, body: Syntax) -> Syntax {
    let declaration = Syntax::node(
        parser_kind(&["Term", "letIdDecl"]),
        vec![
            Syntax::node(parser_kind(&["Term", "letId"]), vec![identifier(name)]),
            null(vec![]),
            null(vec![]),
            atom(":="),
            value,
        ],
    );
    Syntax::node(
        parser_kind(&["Term", "let"]),
        vec![
            atom("let"),
            Syntax::node(parser_kind(&["Term", "letConfig"]), vec![null(vec![])]),
            Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]),
            atom(";"),
            body,
        ],
    )
}
fn invalid() -> NatDefinitionElabError {
    failure(SourceInferenceError::Match(
        matching::MatchError::InvalidPattern,
    ))
}
fn sequence(syntax: &Syntax) -> Result<Vec<&Syntax>, NatDefinitionElabError> {
    let elements = expect_null_args(syntax, "pattern matrix columns")?;
    if elements.is_empty() || elements.len() % 2 == 0 {
        return Err(invalid());
    }
    let mut columns = Vec::new();
    for (index, element) in elements.iter().enumerate() {
        if index % 2 == 0 {
            columns.push(element);
        } else {
            expect_atom(element, ",", "pattern column separator")?;
        }
    }
    Ok(columns)
}
fn flat(pattern: &Syntax) -> bool {
    let variable = |s: &Syntax| {
        matches!(s, Syntax::Ident { .. }) || s.kind() == Some(&parser_kind(&["Term", "hole"]))
    };
    if let Syntax::Node { kind, args, .. } = pattern
        && kind == &parser_kind(&["Term", "app"])
    {
        return matches!(args.as_slice(), [_, Syntax::Node { args, .. }] if args.iter().all(variable));
    }
    variable(pattern) || pattern.kind() == Some(&parser_kind(&["Term", "dotIdent"]))
}
fn complex(syntax: &Syntax) -> bool {
    let Syntax::Node { kind, args, .. } = syntax else {
        return false;
    };
    if kind != &parser_kind(&["Term", "match"]) || args.len() != 6 {
        return false;
    }
    let Ok(discriminants) = expect_null_args(&args[3], "discriminants") else {
        return false;
    };
    if discriminants.len() != 1 {
        return true;
    }
    let Ok(alts) = expect_node(
        &args[5],
        &parser_kind(&["Term", "matchAlts"]),
        1,
        "alternatives",
    ) else {
        return false;
    };
    let Ok(alts) = expect_null_args(&alts[0], "alternatives") else {
        return false;
    };
    alts.iter().any(|alt| {
        let Ok(alt) = expect_node(alt, &parser_kind(&["Term", "matchAlt"]), 4, "alternative")
        else {
            return false;
        };
        let Ok([row]) = expect_null_args(&alt[1], "pattern row") else {
            return false;
        };
        let Ok([pattern]) = expect_null_args(row, "pattern") else {
            return true;
        };
        !flat(pattern)
    })
}

impl Context {
    fn matrix_name(&mut self) -> Result<Name, NatDefinitionElabError> {
        let id = self.next;
        self.fresh_name()?;
        // Numeric components below anonymous are not spellable source binders.
        // They also satisfy the ordinary backend's unqualified-name invariant.
        Ok(Name::num(Name::anonymous(), id))
    }
    fn copy_pattern_syntax(&mut self, syntax: &Syntax) -> Result<Syntax, NatDefinitionElabError> {
        let mut pending = vec![syntax];
        while let Some(syntax) = pending.pop() {
            self.tick()?;
            if let Syntax::Node { args, .. } = syntax {
                pending.extend(args);
            }
        }
        Ok(syntax.clone())
    }

    /// Parse constructor structure without recursive calls or source reparsing.
    /// Unknown qualified names are not downgraded to binders. Relative heads are
    /// deliberately not merged with a guessed family: the typed backend decides.
    fn matrix_pattern<'a>(
        &mut self,
        syntax: &'a Syntax,
        arena: &mut Vec<Pattern<'a>>,
    ) -> Result<usize, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Syntax),
            Constructor(Head, &'a Syntax, usize),
        }
        let mut pending = vec![Task::Visit(syntax)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Constructor(head, syntax, start) => {
                    let fields = values.split_off(start);
                    values.push(arena.len());
                    arena.push(Pattern::Constructor(Constructor {
                        head,
                        syntax,
                        fields,
                    }));
                }
                Task::Visit(syntax) => {
                    if let Some(inner) = parenthesized_inner(syntax)? {
                        pending.push(Task::Visit(inner));
                        continue;
                    }
                    let (head, arguments) = if let Syntax::Node { kind, args, .. } = syntax
                        && kind == &parser_kind(&["Term", "app"])
                    {
                        let [head, arguments] = args.as_slice() else {
                            return Err(invalid());
                        };
                        (head, expect_null_args(arguments, "constructor fields")?)
                    } else {
                        (syntax, &[][..])
                    };
                    let constructor = match head {
                        Syntax::Node { kind, args, .. }
                            if kind == &parser_kind(&["Term", "dotIdent"]) =>
                        {
                            let [dot, Syntax::Ident { val, .. }] = args.as_slice() else {
                                return Err(invalid());
                            };
                            expect_atom(dot, ".", "relative constructor")?;
                            Some(Head {
                                relative: true,
                                name: val.clone(),
                            })
                        }
                        Syntax::Ident { val, .. } => {
                            if matches!(self.txn.env.find(val), Some(ConstantInfo::Ctor(_))) {
                                Some(Head {
                                    relative: false,
                                    name: val.clone(),
                                })
                            } else if val == &Name::from_components(["true"])
                                || val == &Name::from_components(["false"])
                            {
                                Some(Head {
                                    relative: false,
                                    name: Name::from_components(["Bool"]).append_core(val),
                                })
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    if let Some(head_key) = constructor {
                        pending.push(Task::Constructor(head_key, head, values.len()));
                        pending.extend(arguments.iter().rev().map(Task::Visit));
                    } else {
                        if !arguments.is_empty() {
                            return Err(invalid());
                        }
                        let name = matching::pattern_name(head)?;
                        values.push(arena.len());
                        arena.push(Pattern::Bind(name));
                    }
                }
            }
        }
        values.pop().ok_or_else(invalid)
    }

    fn compile_pattern_matrix(
        &mut self,
        syntax: &Syntax,
        required: &mut Vec<Name>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let parts = expect_node(
            syntax,
            &parser_kind(&["Term", "match"]),
            6,
            "pattern matrix",
        )?;
        expect_empty_null(&parts[1], "generalizing annotation")?;
        expect_empty_null(&parts[2], "explicit motive")?;
        let discriminants = sequence(&parts[3])?;
        let alts = expect_node(
            &parts[5],
            &parser_kind(&["Term", "matchAlts"]),
            1,
            "alternatives",
        )?;
        let alts = expect_null_args(&alts[0], "alternatives")?;
        if alts.is_empty() || alts.len() > 256 || discriminants.len() > 64 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut arena = vec![Pattern::Bind(None)];
        let mut rows = Vec::new();
        for alt in alts {
            self.tick()?;
            let alt = expect_node(alt, &parser_kind(&["Term", "matchAlt"]), 4, "alternative")?;
            let [row] = expect_null_args(&alt[1], "one pattern row")? else {
                return Err(invalid());
            };
            let columns = sequence(row)?;
            if columns.len() != discriminants.len() {
                return Err(invalid());
            }
            let start = arena.len();
            let patterns = columns
                .into_iter()
                .map(|column| self.matrix_pattern(column, &mut arena))
                .collect::<Result<Vec<_>, _>>()?;
            let mut bound = HashSet::new();
            for pattern in &arena[start..] {
                if let Pattern::Bind(Some(name)) = pattern
                    && !bound.insert(name.clone())
                {
                    return Err(failure(SourceInferenceError::Match(
                        matching::MatchError::DuplicateVariable,
                    )));
                }
            }
            let witness = self.fresh_name()?;
            required.push(witness.clone());
            rows.push(Row {
                patterns,
                body: &alt[3],
                bindings: Vec::new(),
                witness,
            });
        }
        let mut inputs = Vec::new();
        let mut subjects = Vec::new();
        for discriminant in discriminants {
            let parts = expect_node(
                discriminant,
                &parser_kind(&["Term", "matchDiscr"]),
                2,
                "discriminant",
            )?;
            expect_empty_null(&parts[0], "discriminant equality annotation")?;
            let fresh = self.matrix_name()?;
            // Retain every original expression, even a wildcard-only column.
            // Every column has a private identity, including global constants.
            // Elimination follows exact local aliases when abstracting motives;
            // the original expression still occurs in precisely this binding.
            subjects.push(fresh.clone());
            inputs.push((fresh, self.copy_pattern_syntax(&parts[1])?));
        }
        enum Task<'a> {
            Build(Matrix<'a>),
            Finish(Name, Vec<Alternative>, usize),
        }
        let mut pending = vec![Task::Build(Matrix { subjects, rows })];
        let mut built = Vec::new();
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Finish(subject, alternatives, start) => {
                    let bodies = built.split_off(start);
                    let alternatives = alternatives
                        .into_iter()
                        .zip(bodies)
                        .map(|(alt, body)| {
                            Syntax::node(
                                parser_kind(&["Term", "matchAlt"]),
                                vec![
                                    atom("|"),
                                    null(vec![null(vec![alt.pattern])]),
                                    atom("=>"),
                                    body,
                                ],
                            )
                        })
                        .collect();
                    built.push(Syntax::node(
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
                            Syntax::node(
                                parser_kind(&["Term", "matchAlts"]),
                                vec![null(alternatives)],
                            ),
                        ],
                    ));
                }
                Task::Build(mut matrix) => {
                    if matrix.rows.is_empty() {
                        return Err(invalid());
                    }
                    if matrix.subjects.is_empty() {
                        let row = matrix.rows.remove(0);
                        let mut body = self.copy_pattern_syntax(row.body)?;
                        body = Syntax::node(
                            parser_kind(&["Term", "matrixBranch"]),
                            vec![identifier(row.witness), body],
                        );
                        // Subjects are private numeric names, so introducing
                        // source aliases is simultaneous even for swapped names.
                        for (name, subject) in row.bindings.into_iter().rev() {
                            self.tick()?;
                            body = bind(name, identifier(subject), body);
                        }
                        built.push(body);
                        continue;
                    }
                    let subject = matrix.subjects.remove(0);
                    // Relative and qualified spellings may denote one head.
                    // Resolve only against explicit admitted constructors in
                    // this column; use the qualified spelling in the generated
                    // match so a foreign family's pattern is never erased.
                    let explicit: Vec<_> = matrix
                        .rows
                        .iter()
                        .filter_map(|row| {
                            let Pattern::Constructor(c) = &arena[row.patterns[0]] else {
                                return None;
                            };
                            if c.head.relative {
                                return None;
                            }
                            match self.txn.env.find(&c.head.name) {
                                Some(ConstantInfo::Ctor(ctor)) => {
                                    Some((c.head.clone(), ctor.induct.clone()))
                                }
                                _ => None,
                            }
                        })
                        .collect();
                    let mut canonical = HashMap::new();
                    for row in &matrix.rows {
                        self.tick()?;
                        let Pattern::Constructor(c) = &arena[row.patterns[0]] else {
                            continue;
                        };
                        let mut head = c.head.clone();
                        if head.relative {
                            for (candidate, family) in &explicit {
                                self.tick()?;
                                if family.append_core(&c.head.name) == candidate.name {
                                    if !head.relative && head != *candidate {
                                        return Err(invalid());
                                    }
                                    head = candidate.clone();
                                }
                            }
                        }
                        canonical.insert(c.head.clone(), head);
                    }
                    let mut heads = Vec::new();
                    for row in &matrix.rows {
                        self.tick()?;
                        if let Pattern::Constructor(constructor) = &arena[row.patterns[0]]
                            && !heads.iter().any(|h: &usize| matches!(&arena[*h], Pattern::Constructor(c) if canonical[&c.head] == canonical[&constructor.head]))
                        { heads.push(row.patterns[0]); }
                    }
                    if heads.is_empty() {
                        for row in &mut matrix.rows {
                            if let Pattern::Bind(Some(name)) = &arena[row.patterns.remove(0)] {
                                row.bindings.push((name.clone(), subject.clone()));
                            }
                        }
                        pending.push(Task::Build(matrix));
                        continue;
                    }
                    let mut branches = Vec::new();
                    let mut alternatives = Vec::new();
                    for pattern in heads {
                        let Pattern::Constructor(constructor) = &arena[pattern] else {
                            unreachable!()
                        };
                        let fields: Vec<_> = (0..constructor.fields.len())
                            .map(|_| self.matrix_name())
                            .collect::<Result<_, _>>()?;
                        let mut rows = Vec::new();
                        for row in &matrix.rows {
                            self.tick()?;
                            let mut copy = row.clone();
                            match &arena[copy.patterns.remove(0)] {
                                Pattern::Constructor(other)
                                    if canonical[&other.head] == canonical[&constructor.head] =>
                                {
                                    if other.fields.len() != fields.len() {
                                        return Err(invalid());
                                    }
                                    copy.patterns.splice(..0, other.fields.iter().copied());
                                }
                                Pattern::Constructor(_) => continue,
                                Pattern::Bind(name) => {
                                    if let Some(name) = name {
                                        copy.bindings.push((name.clone(), subject.clone()));
                                    }
                                    copy.patterns
                                        .splice(..0, std::iter::repeat_n(0, fields.len()));
                                }
                            }
                            rows.push(copy);
                        }
                        let mut subjects = fields.clone();
                        subjects.extend(matrix.subjects.iter().cloned());
                        let resolved = &canonical[&constructor.head];
                        let head = if resolved.relative {
                            self.copy_pattern_syntax(constructor.syntax)?
                        } else {
                            identifier(resolved.name.clone())
                        };
                        let pattern = if fields.is_empty() {
                            head
                        } else {
                            Syntax::node(
                                parser_kind(&["Term", "app"]),
                                vec![head, null(fields.into_iter().map(identifier).collect())],
                            )
                        };
                        alternatives.push(Alternative { pattern });
                        branches.push(Matrix { subjects, rows });
                    }
                    let mut fallback = Vec::new();
                    for row in matrix.rows {
                        if let Pattern::Bind(name) = &arena[row.patterns[0]] {
                            let mut copy = row.clone();
                            copy.patterns.remove(0);
                            if let Some(name) = name {
                                copy.bindings.push((name.clone(), subject.clone()));
                            }
                            fallback.push(copy);
                        }
                    }
                    if !fallback.is_empty() {
                        alternatives.push(Alternative {
                            pattern: wildcard(),
                        });
                        branches.push(Matrix {
                            subjects: matrix.subjects,
                            rows: fallback,
                        });
                    }
                    pending.push(Task::Finish(subject, alternatives, built.len()));
                    pending.extend(branches.into_iter().rev().map(Task::Build));
                }
            }
        }
        let mut result = built.pop().ok_or_else(invalid)?;
        for (name, value) in inputs.into_iter().rev() {
            result = bind(name, value, result);
        }
        Ok(result)
    }

    /// Rebuild once, inside out. Ordinary flat matches are not cloned or changed.
    pub(super) fn lower_pattern_matrices<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<(Cow<'a, Syntax>, Vec<Name>), NatDefinitionElabError> {
        let mut scan = vec![syntax];
        let mut needed = false;
        while let Some(node) = scan.pop() {
            self.tick()?;
            needed |= complex(node);
            if let Syntax::Node { args, .. } = node {
                scan.extend(args);
            }
        }
        if !needed {
            return Ok((Cow::Borrowed(syntax), Vec::new()));
        }
        enum Task<'a> {
            Visit(&'a Syntax),
            Node(&'a Syntax, usize),
        }
        let mut tasks = vec![Task::Visit(syntax)];
        let mut built = Vec::new();
        let mut required = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(node @ Syntax::Node { args, .. }) => {
                    tasks.push(Task::Node(node, built.len()));
                    tasks.extend(args.iter().rev().map(Task::Visit));
                }
                Task::Visit(leaf) => built.push(leaf.clone()),
                Task::Node(Syntax::Node { info, kind, .. }, start) => {
                    let node = Syntax::Node {
                        info: *info,
                        kind: kind.clone(),
                        args: built.split_off(start),
                    };
                    built.push(if complex(&node) {
                        self.compile_pattern_matrix(&node, &mut required)?
                    } else {
                        node
                    });
                }
                _ => unreachable!(),
            }
        }
        Ok((Cow::Owned(built.pop().expect("rewritten root")), required))
    }
}
