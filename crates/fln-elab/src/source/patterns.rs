//! Heap-planned pattern matrices lowered to the ordinary checked match backend.
//!
//! This layer never learns constructors by evaluating a discriminant. It splits
//! source rows in order, retains all discriminants in checked local bindings,
//! and leaves constructor typing, coverage and index equations to the existing
//! elaborator. Every original row has an elaboration witness: a redundant row
//! cannot hide an ill-typed body when a generated fallback is unnecessary.
use super::*;
mod literals;
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
    syntax: Cow<'a, Syntax>,
    fields: Vec<usize>,
}
enum Pattern<'a> {
    Bind(Option<Name>),
    Constructor(Constructor<'a>),
    Literal(literals::LiteralPattern<'a>),
}
#[derive(Clone)]
struct Row<'a> {
    patterns: Vec<usize>,
    bindings: Vec<(Name, Name)>,
    body: &'a Syntax,
    witness: Name,
}
struct Matrix<'a> {
    recursive_root: bool,
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
fn complex(syntax: &Syntax, environment: &Environment) -> bool {
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
        if !flat(pattern) {
            return true;
        }
        // A catch-all can bind a value of an abstract type without any
        // inductive-family lookup. Let the matrix compiler retain its checked
        // input binding and detect redundant rows instead of demanding a
        // constructor recursor for an otherwise ordinary function argument.
        match pattern {
            Syntax::Ident { val, .. } => {
                !matches!(environment.find(val), Some(ConstantInfo::Ctor(_)))
                    && val != &Name::from_components(["true"])
                    && val != &Name::from_components(["false"])
            }
            Syntax::Node { kind, .. } => kind == &parser_kind(&["Term", "hole"]),
            _ => false,
        }
    })
}

/// The element patterns of `⟨p, …⟩`, if `syntax` is one.
fn anonymous_elements(syntax: &Syntax) -> Result<Option<Vec<&Syntax>>, NatDefinitionElabError> {
    let kind = parser_kind(&["Term", "anonymousCtor"]);
    if syntax.kind() != Some(&kind) {
        return Ok(None);
    }
    let parts = expect_node(syntax, &kind, 3, "anonymous constructor pattern")?;
    expect_atom(&parts[0], "⟨", "anonymous constructor opener")?;
    expect_atom(&parts[2], "⟩", "anonymous constructor closer")?;
    let items = expect_null_args(&parts[1], "anonymous constructor fields")?;
    let mut elements = Vec::with_capacity(items.len().div_ceil(2));
    for (index, item) in items.iter().enumerate() {
        if index % 2 == 0 {
            elements.push(item);
        } else {
            expect_atom(item, ",", "anonymous constructor separator")?;
        }
    }
    if items.len() % 2 == 0 && !items.is_empty() {
        return Err(invalid());
    }
    Ok(Some(elements))
}

/// The head standing for "the only constructor" in a generated match.
pub(super) fn anonymous_head() -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "anonymousCtor"]),
        vec![atom("⟨"), null(Vec::new()), atom("⟩")],
    )
}

/// `if let p := e then a else b` is `match e with | p => a | _ => b` (`termIfLet`'s macro,
/// `Init/Notation.lean`).
fn expand_if_let(mut syntax: Syntax, pattern: bool) -> Syntax {
    let rewrite = !pattern
        && matches!(&syntax, Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["termIfLet"]) && args.len() == 9);
    if !rewrite {
        return syntax;
    }
    let Syntax::Node { args, .. } = &mut syntax else {
        unreachable!("checked notation");
    };
    let mut take = |index: usize| std::mem::replace(&mut args[index], null(vec![]));
    let (case, value, yes, no) = (take(2), take(4), take(6), take(8));
    let alternative = |pattern: Syntax, body: Syntax| {
        Syntax::node(
            parser_kind(&["Term", "matchAlt"]),
            vec![atom("|"), null(vec![null(vec![pattern])]), atom("=>"), body],
        )
    };
    Syntax::node(
        parser_kind(&["Term", "match"]),
        vec![
            atom("match"),
            null(vec![]),
            null(vec![]),
            null(vec![Syntax::node(
                parser_kind(&["Term", "matchDiscr"]),
                vec![null(vec![]), value],
            )]),
            atom("with"),
            Syntax::node(
                parser_kind(&["Term", "matchAlts"]),
                vec![null(vec![
                    alternative(case, yes),
                    alternative(
                        Syntax::node(parser_kind(&["Term", "hole"]), vec![atom("_")]),
                        no,
                    ),
                ])],
            ),
        ],
    )
}

/// `e matches p | q` is `match e with | p => true | q => true | _ => false` (the macro of
/// `Lean.«term_Matches_|»`, `Init/Notation.lean`, which shares one `true` between the
/// alternatives; one alternative per pattern means the same).
fn expand_matches(mut syntax: Syntax, pattern: bool) -> Syntax {
    let rewrite = !pattern
        && matches!(&syntax, Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["Lean", "term_Matches_|"]) && args.len() == 3);
    if !rewrite {
        return syntax;
    }
    let Syntax::Node { args, .. } = &mut syntax else {
        unreachable!("checked notation");
    };
    let value = std::mem::replace(&mut args[0], null(vec![]));
    let Syntax::Node { args: listed, .. } = &mut args[2] else {
        return syntax;
    };
    let alternative = |pattern: Syntax, body: Syntax| {
        Syntax::node(
            parser_kind(&["Term", "matchAlt"]),
            vec![atom("|"), null(vec![null(vec![pattern])]), atom("=>"), body],
        )
    };
    let mut alternatives: Vec<Syntax> = listed
        .iter()
        .step_by(2)
        .map(|pattern| {
            alternative(
                pattern.clone(),
                identifier(Name::from_components(["Bool", "true"])),
            )
        })
        .collect();
    alternatives.push(alternative(
        wildcard(),
        identifier(Name::from_components(["Bool", "false"])),
    ));
    Syntax::node(
        parser_kind(&["Term", "match"]),
        vec![
            atom("match"),
            null(vec![]),
            null(vec![]),
            null(vec![Syntax::node(
                parser_kind(&["Term", "matchDiscr"]),
                vec![null(vec![]), value],
            )]),
            atom("with"),
            Syntax::node(
                parser_kind(&["Term", "matchAlts"]),
                vec![null(alternatives)],
            ),
        ],
    )
}

/// Whether `syntax` is a term `let` whose declaration is a pattern (`letPatDecl`, `let ⟨a, b⟩ := p`)
/// with no `letConfig` option, which [`expand_let_pattern`] rewrites.
fn let_pattern(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Term", "let"])
            && args.len() == 5
            && matches!(&args[1], Syntax::Node { kind, args: config, .. }
                if kind == &parser_kind(&["Term", "letConfig"])
                    && matches!(config.as_slice(), [Syntax::Node { args: options, .. }]
                        if options.is_empty()))
            && matches!(&args[2], Syntax::Node { kind, args: declaration, .. }
                if kind == &parser_kind(&["Term", "letDecl"])
                    && matches!(declaration.as_slice(), [Syntax::Node { kind, args: parts, .. }]
                        if kind == &parser_kind(&["Term", "letPatDecl"])
                            && parts.len() == 5
                            && parts[0].kind() != Some(&parser_kind(&["Term", "hole"]))
                            && matches!(&parts[1], Syntax::Node { args, .. } if args.is_empty()))))
}

/// `let p := v; b` with a pattern is `match v with | p => b`, and `let p : T := v; b` is
/// `match (v : T) with | p => b` (`elabLetDeclCore`'s `letPatDecl` case, `Lean/Elab/Binders.lean`).
fn expand_let_pattern(mut syntax: Syntax, pattern: bool) -> Syntax {
    if pattern || !let_pattern(&syntax) {
        return syntax;
    }
    let Syntax::Node { args, .. } = &mut syntax else {
        unreachable!("checked let");
    };
    let body = std::mem::replace(&mut args[4], null(vec![]));
    let Syntax::Node {
        args: declaration, ..
    } = &mut args[2]
    else {
        unreachable!("checked declaration");
    };
    let Syntax::Node { args: parts, .. } = &mut declaration[0] else {
        unreachable!("checked pattern declaration");
    };
    let case = std::mem::replace(&mut parts[0], null(vec![]));
    let value = std::mem::replace(&mut parts[4], null(vec![]));
    let annotation = match &mut parts[2] {
        Syntax::Node { args: spec, .. } => match spec.as_mut_slice() {
            [Syntax::Node { args: typed, .. }] if typed.len() == 2 => {
                Some(std::mem::replace(&mut typed[1], null(vec![])))
            }
            _ => None,
        },
        _ => None,
    };
    let value = match annotation {
        Some(type_) => Syntax::node(
            parser_kind(&["Term", "typeAscription"]),
            vec![atom("("), value, atom(":"), null(vec![type_]), atom(")")],
        ),
        None => value,
    };
    Syntax::node(
        parser_kind(&["Term", "match"]),
        vec![
            atom("match"),
            null(vec![]),
            null(vec![]),
            null(vec![Syntax::node(
                parser_kind(&["Term", "matchDiscr"]),
                vec![null(vec![]), value],
            )]),
            atom("with"),
            Syntax::node(
                parser_kind(&["Term", "matchAlts"]),
                vec![null(vec![Syntax::node(
                    parser_kind(&["Term", "matchAlt"]),
                    vec![atom("|"), null(vec![null(vec![case])]), atom("=>"), body],
                )])],
            ),
        ],
    )
}

/// `‹T›` is `(by assumption : T)` (`macro "‹" type:term "›" : term`, `Init/Tactics.lean`).
fn expand_assumption(mut syntax: Syntax, pattern: bool) -> Syntax {
    let rewrite = !pattern
        && matches!(&syntax, Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["term‹_›"]) && args.len() == 3);
    if !rewrite {
        return syntax;
    }
    let Syntax::Node { args, .. } = &mut syntax else {
        unreachable!("checked notation");
    };
    let type_ = std::mem::replace(&mut args[1], null(vec![]));
    let proof = Syntax::node(
        parser_kind(&["Term", "byTactic"]),
        vec![
            atom("by"),
            Syntax::node(
                parser_kind(&["Tactic", "tacticSeq"]),
                vec![Syntax::node(
                    parser_kind(&["Tactic", "tacticSeq1Indented"]),
                    vec![null(vec![Syntax::node(
                        parser_kind(&["Tactic", "assumption"]),
                        vec![atom("assumption")],
                    )])],
                )],
            ),
        ],
    );
    Syntax::node(
        parser_kind(&["Term", "typeAscription"]),
        vec![atom("("), proof, atom(":"), null(vec![type_]), atom(")")],
    )
}

/// Whether `syntax` is a lambda with an anonymous-constructor binder, which
/// [`expand_fun_patterns`] rewrites.
fn fun_patterns(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Term", "fun"])
            && matches!(args.get(1), Some(Syntax::Node { kind, args: basic, .. })
                if kind == &parser_kind(&["Term", "basicFun"])
                    && matches!(basic.first(), Some(Syntax::Node { args: binders, .. })
                        if binders.iter().any(pattern_binder))))
}

/// An anonymous-constructor (`⟨a, b⟩`) or tuple (`(a, b)`) lambda binder.
fn pattern_binder(binder: &Syntax) -> bool {
    binder.kind() == Some(&parser_kind(&["Term", "anonymousCtor"]))
        || binder.kind() == Some(&parser_kind(&["Term", "tuple"]))
}

/// `fun ⟨a, b⟩ c => e`, a lambda with an anonymous-constructor binder, is the pattern lambda
/// `fun | ⟨a, b⟩, c => e`: the pin's `expandFunBinders` matches every written binder against a
/// fresh local the same way, and a name or `_` binds as a pattern does. With a typed binder
/// group or a result annotation the lambda is left as written, and refused.
fn expand_fun_patterns(mut syntax: Syntax, pattern: bool) -> Syntax {
    let rewrite = !pattern
        && matches!(&syntax, Syntax::Node { kind, args, .. }
        if kind == &parser_kind(&["Term", "fun"])
            && matches!(args.get(1), Some(Syntax::Node { kind, args: basic, .. })
                if kind == &parser_kind(&["Term", "basicFun"])
                    && basic.len() == 4
                    && matches!(&basic[1], Syntax::Node { args, .. } if args.is_empty())
                    && matches!(&basic[0], Syntax::Node { args: binders, .. }
                        if binders.iter().any(pattern_binder)
                            && binders.iter().all(|b| {
                                pattern_binder(b)
                                    || matches!(b, Syntax::Ident { .. })
                                    || b.kind() == Some(&parser_kind(&["Term", "hole"]))
                            }))));
    if !rewrite {
        return syntax;
    }
    let Syntax::Node { args, .. } = &mut syntax else {
        unreachable!("checked lambda");
    };
    let Syntax::Node { args: basic, .. } = &mut args[1] else {
        unreachable!("checked basicFun");
    };
    let body = std::mem::replace(&mut basic[3], null(vec![]));
    let arrow = std::mem::replace(&mut basic[2], null(vec![]));
    let Syntax::Node { args: binders, .. } = &mut basic[0] else {
        unreachable!("checked binders");
    };
    let mut patterns = Vec::new();
    for (index, binder) in std::mem::take(binders).into_iter().enumerate() {
        if index != 0 {
            patterns.push(atom(","));
        }
        patterns.push(binder);
    }
    args[1] = Syntax::node(
        parser_kind(&["Term", "matchAlts"]),
        vec![null(vec![Syntax::node(
            parser_kind(&["Term", "matchAlt"]),
            vec![atom("|"), null(vec![null(patterns)]), arrow, body],
        )])],
    );
    syntax
}

/// A field defined by equations, `toString | true => "t" | false => "f"`, is the field
/// `toString := fun | true => "t" | false => "f"`. The equations become the pattern lambda when
/// their own node is rebuilt (and are compiled there, as any `fun | …`); the field holding a bare
/// lambda in its definition slot, which only this produces, then gets its `:=` definition.
fn expand_field_equations(mut syntax: Syntax, pattern: bool) -> Syntax {
    if pattern {
        return syntax;
    }
    let equations = parser_kind(&["Term", "structInstFieldEqns"]);
    let field = parser_kind(&["Term", "structInstField"]);
    let lambda = parser_kind(&["Term", "fun"]);
    match &mut syntax {
        Syntax::Node { kind, args, .. }
            if *kind == equations
                && args.len() == 2
                && matches!(&args[0], Syntax::Node { args, .. } if args.is_empty()) =>
        {
            let alternatives = std::mem::replace(&mut args[1], null(vec![]));
            Syntax::node(lambda, vec![atom("fun"), alternatives])
        }
        Syntax::Node { kind, args, .. } if *kind == field && args.len() == 2 => {
            if let Syntax::Node { args: payload, .. } = &mut args[1]
                && payload.len() == 3
                && payload[2].kind() == Some(&lambda)
            {
                let value = std::mem::replace(&mut payload[2], null(vec![]));
                payload[2] = Syntax::node(
                    parser_kind(&["Term", "structInstFieldDef"]),
                    vec![atom(":="), null(vec![]), value],
                );
            }
            syntax
        }
        _ => syntax,
    }
}

fn pattern_function(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node {kind,args,..}
        if kind == &parser_kind(&["Term","fun"])
        && matches!(args.get(1), Some(Syntax::Node {kind,..})
            if kind == &parser_kind(&["Term","matchAlts"])))
}

impl Context {
    /// Pattern lambdas are ordinary lambdas over fresh private names. Domain
    /// inference/checking stays in the existing lambda elaborator. The body's
    /// original alternatives go through the same matrix compiler as match.
    fn compile_pattern_function(
        &mut self,
        mut syntax: Syntax,
        required: &mut Vec<Name>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let Syntax::Node { args, .. } = &mut syntax else {
            return Err(invalid());
        };
        if args.len() != 2 {
            return Err(invalid());
        }
        let alternatives = args.pop().expect("validated pattern function");
        let keyword = args.pop().expect("validated function keyword");
        if !matches!(&keyword, Syntax::Atom {val,..} if val == "fun" || val == "λ") {
            return Err(invalid());
        }
        let arity = self.equation_arity(&alternatives)?;
        let mut names = Vec::new();
        let mut discriminants = Vec::new();
        for index in 0..arity {
            self.tick()?;
            let serial = self.next;
            let _ = self.fresh_name()?;
            let name = Name::num(Name::anonymous(), serial);
            names.push(identifier(name.clone()));
            if index != 0 {
                discriminants.push(atom(","));
            }
            discriminants.push(Syntax::node(
                parser_kind(&["Term", "matchDiscr"]),
                vec![null(vec![]), identifier(name)],
            ));
        }
        let body = Syntax::node(
            parser_kind(&["Term", "match"]),
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(discriminants),
                atom("with"),
                alternatives,
            ],
        );
        let body = self.compile_pattern_matrix(&body, required, None)?;
        Ok(Syntax::node(
            parser_kind(&["Term", "fun"]),
            vec![
                keyword,
                Syntax::node(
                    parser_kind(&["Term", "basicFun"]),
                    vec![null(names), null(vec![]), atom("=>"), body],
                ),
            ],
        ))
    }

    fn matrix_name(&mut self) -> Result<Name, NatDefinitionElabError> {
        let id = self.next;
        self.fresh_name()?;
        // Numeric components below anonymous are not spellable source binders.
        // They also satisfy the ordinary backend's unqualified-name invariant.
        Ok(Name::num(Name::anonymous(), id))
    }
    pub(super) fn copy_pattern_syntax(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
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
            Constructor(Head, Cow<'a, Syntax>, usize),
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
                    // `⟨p, …⟩`: a constructor pattern whose head is the column type's only
                    // constructor. The head is the empty `⟨⟩`, which the ordinary match
                    // backend resolves against the discriminant's family.
                    if let Some(elements) = anonymous_elements(syntax)? {
                        pending.push(Task::Constructor(
                            Head {
                                relative: true,
                                name: Name::anonymous(),
                            },
                            Cow::Owned(anonymous_head()),
                            values.len(),
                        ));
                        pending.extend(elements.into_iter().rev().map(Task::Visit));
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
                    if let Some(literal) = self.decode_pattern_literal(head)? {
                        if !arguments.is_empty() {
                            return Err(invalid());
                        }
                        values.push(arena.len());
                        arena.push(Pattern::Literal(literal));
                        continue;
                    }
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
                            let resolved = self
                                .resolve_source_name(val)?
                                .unwrap_or_else(|| val.clone());
                            let val = &resolved;
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
                        pending.push(Task::Constructor(
                            head_key,
                            Cow::Borrowed(head),
                            values.len(),
                        ));
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

    pub(super) fn compile_pattern_matrix(
        &mut self,
        syntax: &Syntax,
        required: &mut Vec<Name>,
        recursive_column: Option<usize>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let recursive_root = recursive_column.is_some();
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
        // Structural selection changes the decision-tree split, not argument
        // order or row priority. Original inputs retain their checked bindings.
        let root_column = recursive_column.unwrap_or(0);
        if root_column != 0 {
            if root_column >= subjects.len() {
                return Err(invalid());
            }
            subjects.swap(0, root_column);
            for row in &mut rows {
                self.tick()?;
                row.patterns.swap(0, root_column);
            }
        }
        enum Task<'a> {
            Build(Matrix<'a>),
            Finish(Name, Vec<Alternative>, usize, bool),
            Literal(Syntax, usize),
        }
        let mut pending = vec![Task::Build(Matrix {
            subjects,
            rows,
            recursive_root,
        })];
        let mut built = Vec::new();
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Literal(test, start) => {
                    let bodies = built.split_off(start);
                    if bodies.len() != 2 {
                        return Err(invalid());
                    }
                    let alternatives = ["true", "false"]
                        .into_iter()
                        .zip(bodies)
                        .map(|(name, body)| {
                            Syntax::node(
                                parser_kind(&["Term", "matchAlt"]),
                                vec![
                                    atom("|"),
                                    null(vec![null(vec![identifier(Name::from_components([
                                        "Bool", name,
                                    ]))])]),
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
                                vec![null(vec![]), test],
                            )]),
                            atom("with"),
                            Syntax::node(
                                parser_kind(&["Term", "matchAlts"]),
                                vec![null(alternatives)],
                            ),
                        ],
                    ));
                }
                Task::Finish(subject, alternatives, start, root) => {
                    let bodies = built.split_off(start);
                    let alternatives = alternatives
                        .into_iter()
                        .zip(bodies)
                        .map(|(alt, mut body)| {
                            self.tick()?;
                            if root {
                                // Re-evaluate other columns in the generalized
                                // recursive branch, not in the captured caller.
                                for (name, value) in inputs.iter().rev() {
                                    body =
                                        bind(name.clone(), self.copy_pattern_syntax(value)?, body);
                                }
                            }
                            Ok(Syntax::node(
                                parser_kind(&["Term", "matchAlt"]),
                                vec![
                                    atom("|"),
                                    null(vec![null(vec![alt.pattern])]),
                                    atom("=>"),
                                    body,
                                ],
                            ))
                        })
                        .collect::<Result<_, NatDefinitionElabError>>()?;
                    let discriminant = if root {
                        inputs[root_column].1.clone()
                    } else {
                        identifier(subject)
                    };
                    built.push(Syntax::node(
                        parser_kind(&["Term", "matchMatrix"]),
                        vec![
                            atom("match"),
                            null(vec![]),
                            null(vec![]),
                            null(vec![Syntax::node(
                                parser_kind(&["Term", "matchDiscr"]),
                                vec![null(vec![]), discriminant],
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
                            body = Syntax::node(
                                parser_kind(&["Term", "matrixAlias"]),
                                vec![identifier(name), identifier(subject), body],
                            );
                        }
                        built.push(body);
                        continue;
                    }
                    let subject = matrix.subjects.remove(0);
                    if let Some((test, hit, miss)) =
                        self.literal_matrix_split(&mut matrix, &subject, &mut arena)?
                    {
                        pending.push(Task::Literal(test, built.len()));
                        pending.push(Task::Build(miss));
                        pending.push(Task::Build(hit));
                        continue;
                    }
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
                        if matrix.recursive_root {
                            return Err(failure(SourceInferenceError::Recursion(
                                recursion::RecursionError::RootMatchRequired,
                            )));
                        }
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
                                Pattern::Literal(_) => return Err(invalid()),
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
                            self.copy_pattern_syntax(&constructor.syntax)?
                        } else {
                            // This name was resolved against the admitted
                            // environment already. Preserve that identity on
                            // re-entry: an enclosing namespace may contain a
                            // different declaration with the same suffix.
                            let name =
                                if self.source_scope.user_name(&resolved.name) != resolved.name {
                                    // A current-module private core name is
                                    // already exact. `_root_` is a source prefix;
                                    // putting it before an internal numeric name
                                    // would make that identity unrecognizable.
                                    resolved.name.clone()
                                } else {
                                    Name::from_components(["_root_"]).append_core(&resolved.name)
                                };
                            identifier(name)
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
                        branches.push(Matrix {
                            subjects,
                            rows,
                            recursive_root: false,
                        });
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
                            recursive_root: false,
                            subjects: matrix.subjects,
                            rows: fallback,
                        });
                    }
                    pending.push(Task::Finish(
                        subject,
                        alternatives,
                        built.len(),
                        matrix.recursive_root,
                    ));
                    pending.extend(branches.into_iter().rev().map(Task::Build));
                }
            }
        }
        let mut result = built.pop().ok_or_else(invalid)?;
        if !recursive_root {
            for (name, value) in inputs.into_iter().rev() {
                result = bind(name, value, result);
            }
        }
        Ok(result)
    }

    /// Lower a generated pattern conditional at its construction site. Its
    /// branch bodies have already been processed by the do worklist, so do not
    /// walk or expand them again. The ordinary matrix compiler and coverage
    /// witnesses remain authoritative for the new match.
    pub(super) fn lower_do_pattern_match(
        &mut self,
        syntax: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        // The ordinary flat-match checker already owns exhaustive constructor
        // arms and discriminant equality binders. Use the identical selection
        // as the surrounding pattern walk, rather than forcing those matches
        // through a matrix pass that cannot preserve named equalities yet.
        if !complex(&syntax, &self.txn.env) {
            return Ok(syntax);
        }
        let mut required = Vec::new();
        let body = self.compile_pattern_matrix(&syntax, &mut required, None)?;
        Ok(if required.is_empty() {
            body
        } else {
            Syntax::node(
                parser_kind(&["Term", "matrixScope"]),
                vec![null(required.into_iter().map(identifier).collect()), body],
            )
        })
    }

    /// Rebuild once, inside out. Ordinary flat matches are not cloned or changed.
    pub(super) fn lower_pattern_matrices<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Cow<'a, Syntax>, NatDefinitionElabError> {
        let mut scan = vec![syntax];
        let mut needed = false;
        let mut local_roots = HashSet::new();
        while let Some(node) = scan.pop() {
            self.tick()?;
            if node.kind() == Some(&parser_kind(&["Term", "localRecValue"])) {
                continue;
            }
            needed |= complex(node, &self.txn.env)
                || pattern_function(node)
                || collections::is_notation(node)
                || cdot::is_cdot(node)
                || binders::is_exists(node)
                || binders::is_binder_predicate(node)
                || record_terms::is_field_notation(node)
                || fun_patterns(node)
                || node.kind() == Some(&Name::from_components(["term‹_›"]))
                || node.kind() == Some(&Name::from_components(["termIfLet"]))
                || let_pattern(node)
                || node.kind() == Some(&Name::from_components(["Lean", "term_Matches_|"]))
                || node.kind() == Some(&parser_kind(&["Term", "structInstFieldEqns"]))
                || node.kind() == Some(&parser_kind(&["Term", "do"]));
            if let Syntax::Node { args, .. } = node {
                if node.kind() == Some(&parser_kind(&["Term", "letrec"])) {
                    let binding = self.let_parts(args, false, true)?;
                    let root = self.recursive_lambda_body(binding.value)?;
                    local_roots.insert(std::ptr::from_ref(root));
                }
                scan.extend(args);
            }
        }
        if !needed {
            return Ok(Cow::Borrowed(syntax));
        }
        let mut root = syntax;
        while let Some(inner) = parenthesized_inner(root)? {
            self.tick()?;
            root = inner;
        }
        enum Task<'a> {
            Visit(&'a Syntax, bool),
            Node(&'a Syntax, usize, bool),
        }
        let alternative_kind = parser_kind(&["Term", "matchAlt"]);
        let mut tasks = vec![Task::Visit(syntax, false)];
        let mut built = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(node, _)
                    if node.kind() == Some(&parser_kind(&["Term", "localRecValue"])) =>
                {
                    built.push(self.copy_pattern_syntax(node)?);
                }
                Task::Visit(node @ Syntax::Node { kind, args, .. }, pattern) => {
                    tasks.push(Task::Node(node, built.len(), pattern));
                    for (index, argument) in args.iter().enumerate().rev() {
                        self.tick()?;
                        let pattern = if kind == &alternative_kind
                            || kind == &parser_kind(&["Term", "doIfLet"])
                        {
                            index == 1
                        } else if kind == &Name::from_components(["termIfLet"])
                            || kind == &Name::from_components(["Lean", "term_Matches_|"])
                        {
                            index == 2
                        } else if kind == &parser_kind(&["Term", "doPatDecl"])
                            || kind == &parser_kind(&["Term", "letPatDecl"])
                        {
                            pattern || index == 0
                        } else {
                            pattern
                        };
                        tasks.push(Task::Visit(argument, pattern));
                    }
                }
                Task::Visit(leaf, _) => built.push(leaf.clone()),
                Task::Node(original @ Syntax::Node { info, kind, .. }, start, pattern) => {
                    let node = Syntax::Node {
                        info: *info,
                        kind: kind.clone(),
                        args: built.split_off(start),
                    };
                    // `·` first: collection notation would turn a tuple into `Prod.mk`.
                    let node = self.expand_cdot_node(node, pattern)?;
                    let node = self.expand_collection_node(node, pattern)?;
                    let node = self.expand_do_node(node, pattern)?;
                    let node = self.expand_binder_predicate_node(node, pattern)?;
                    let node = self.expand_exists_node(node, pattern)?;
                    let node = self.expand_record_field_node(node, pattern)?;
                    let node = self.expand_offset_pattern(node, pattern)?;
                    let node = expand_fun_patterns(node, pattern);
                    let node = expand_field_equations(node, pattern);
                    let node = expand_assumption(node, pattern);
                    let node = expand_if_let(node, pattern);
                    let node = expand_let_pattern(node, pattern);
                    let node = expand_matches(node, pattern);
                    let mut required = Vec::new();
                    let node = if local_roots.contains(&std::ptr::from_ref(original))
                        && complex(&node, &self.txn.env)
                    {
                        // Keep all bodies inside this owned syntax tree. The
                        // term driver can borrow and retry them on its heap
                        // worklist, without recursive host calls or leaking an
                        // arena. Header identities and typing are resolved only
                        // when the local definition is actually elaborated.
                        self.local_recursive_matrices(node)?
                    } else if pattern_function(&node) {
                        self.compile_pattern_function(node, &mut required)?
                    } else if complex(&node, &self.txn.env) {
                        let column = if std::ptr::eq(original, root) {
                            self.recursion.as_mut().filter(|r| r.pending).map(|r| {
                                r.matrix = true;
                                r.column
                            })
                        } else {
                            None
                        };
                        self.compile_pattern_matrix(&node, &mut required, column)?
                    } else {
                        node
                    };
                    // Coverage belongs to this match's actual elaboration, not
                    // to an unchosen tactic alternative elsewhere in the term.
                    built.push(if required.is_empty() {
                        node
                    } else {
                        Syntax::node(
                            parser_kind(&["Term", "matrixScope"]),
                            vec![null(required.into_iter().map(identifier).collect()), node],
                        )
                    });
                }
                _ => unreachable!(),
            }
        }
        Ok(Cow::Owned(built.pop().expect("rewritten root")))
    }

    /// The original matrix, ordinary decision tree, then one tree per possible
    /// root column. Trees are only candidate syntax: each selected body still
    /// passes the ordinary coverage, termination, type, and kernel checks.
    /// An impossible structural split is retained as a missing candidate, not
    /// turned into a failure in an unchosen tactic branch.
    fn local_recursive_matrices(&mut self, node: Syntax) -> Result<Syntax, NatDefinitionElabError> {
        let parts = expect_node(
            &node,
            &parser_kind(&["Term", "match"]),
            6,
            "local recursive matrix",
        )?;
        let discriminants = expect_null_args(&parts[3], "local recursive discriminants")?;
        let columns = discriminants.len().div_ceil(2);
        let mut bodies = vec![self.copy_pattern_syntax(&node)?];
        for column in std::iter::once(None).chain((0..columns).map(Some)) {
            self.tick()?;
            let mut required = Vec::new();
            let body = match self.compile_pattern_matrix(&node, &mut required, column) {
                Ok(body) => body,
                Err(NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                    recursion::RecursionError::RootMatchRequired,
                ))) if column.is_some() => {
                    bodies.push(Syntax::Missing);
                    continue;
                }
                Err(problem) => return Err(problem),
            };
            bodies.push(if required.is_empty() {
                body
            } else {
                Syntax::node(
                    parser_kind(&["Term", "matrixScope"]),
                    vec![null(required.into_iter().map(identifier).collect()), body],
                )
            });
        }
        Ok(Syntax::node(
            parser_kind(&["Term", "localRecValue"]),
            bodies,
        ))
    }
}
