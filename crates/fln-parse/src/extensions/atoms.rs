//! Macro dispatch for the pin's atomic syntax kinds.
//!
//! An identifier or literal is expanded where it denotes a term. Names naming
//! declarations, binders, fields, universes and syntax data are not terms;
//! eagerly rewriting those leaves changes the program before elaboration.
use super::*;

pub(super) fn is_kind(kind: &Name) -> bool {
    ["num", "str", "ident", "char", "scientific", "name"]
        .iter()
        .any(|name| *kind == Name::from_components([*name]))
}

pub(super) fn valid_pattern(kind: &Name, operands: &[Syntax]) -> bool {
    let [operand] = operands else {
        return false;
    };
    match operand {
        Syntax::Ident { .. } => *kind == Name::from_components(["ident"]),
        Syntax::Node { kind: actual, .. } => {
            actual == kind || (actual.parent() == *kind && antiquotation_name(operand).is_some())
        }
        _ => false,
    }
}

pub(super) fn captures_whole_kind(rule: &NotationRule) -> bool {
    rule.pattern
        .as_ref()
        .and_then(node_args)
        .is_some_and(|args| matches!(args, [capture] if antiquotation_name(capture).is_some()))
}

/// Keep quoted identifiers syntactic throughout recursive macro matching.
/// The native elaborator then consumes their definition-site declarations as
/// absolute names. Retain the original source spans and every hygiene scope.
pub(super) fn anchor_preresolved(syntax: &mut Syntax) -> Result<(), &'static str> {
    let mut pending = vec![syntax];
    while let Some(node) = pending.pop() {
        match node {
            Syntax::Node { args, .. } => pending.extend(args.iter_mut()),
            Syntax::Ident {
                val, preresolved, ..
            } => {
                if let [Preresolved::Decl { name, fields }] = preresolved.as_slice()
                    && fields.is_empty()
                {
                    let mut scopes = fln_syntax::hygiene::extract_macro_scopes(val)
                        .map_err(|_| "a preresolved name with malformed macro scopes")?;
                    scopes.name = Name::from_components(["_root_"]).append_core(name);
                    *val = scopes.review();
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// A punned field denotes both a raw field label and a term with that spelling.
/// Materialize the latter before walking, as the structure elaborator does,
/// so an identifier macro changes its value without renaming the field.
pub(super) fn field_abbreviation(syntax: &Syntax) -> Option<Syntax> {
    let Syntax::Node { info, kind, args } = syntax else {
        return None;
    };
    if !kind_is(kind, "Term", "structInstField") {
        return None;
    }
    let [label, payload] = args.as_slice() else {
        return None;
    };
    if !null_args(payload).is_some_and(<[Syntax]>::is_empty) {
        return None;
    }
    let [name @ Syntax::Ident { .. }, fields] = node_args(label)? else {
        return None;
    };
    if !null_args(fields).is_some_and(<[Syntax]>::is_empty) {
        return None;
    }
    Some(Syntax::Node {
        info: *info,
        kind: kind.clone(),
        args: vec![
            label.clone(),
            null_node(vec![
                null_node(Vec::new()),
                null_node(Vec::new()),
                Syntax::node(
                    crate::parser_kind(&["Term", "structInstFieldDef"]),
                    vec![
                        Syntax::atom(SourceInfo::None, ":="),
                        null_node(Vec::new()),
                        name.clone(),
                    ],
                ),
            ]),
        ],
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Position {
    Term,
    AppHead,
    Binders,
    Binder,
    FieldPayload,
    Raw,
}

fn kind_is(kind: &Name, category: &str, leaf: &str) -> bool {
    *kind == crate::parser_kind(&[category, leaf])
}

pub(super) fn raw_node(kind: &Name) -> bool {
    [
        "declId",
        "declModifiers",
        "docComment",
        "moduleDoc",
        "versoCommentBody",
        "print",
        "printAxioms",
        "printPrefix",
        "printFields",
        "attribute",
        "export",
        "deriving",
        "optDeriving",
        "structCtor",
    ]
    .iter()
    .any(|leaf| kind_is(kind, "Command", leaf))
        || [
            "quotedName",
            "quot",
            "quotSeq",
            "dynamicQuot",
            "type",
            "sort",
            "letId",
            "structInstLVal",
            "attrKind",
            "letConfig",
            "explicitUniv",
        ]
        .iter()
        .any(|leaf| kind_is(kind, "Term", leaf))
        || [
            "intros",
            "renameI",
            "rename_i",
            "quot",
            "revert",
            "injections",
            "congr",
            "rotateLeft",
            "rotateRight",
            "traceMessage",
            "caseArg",
            "inductionAltLHS",
            "location",
        ]
        .iter()
        .any(|leaf| kind_is(kind, "Tactic", leaf))
        || *kind == Name::from_components(["Lean", "binderIdent"])
        || *kind == crate::parser_kind(&["Tactic", "rcasesPat", "one"])
        || kind.parent() == crate::parser_kind(&["Level"])
}

/// The role of one child in the parser's actual syntax tree. The wrapper
/// positions are shared by source declarations, quoted expansions, and replay.
pub(super) fn child(kind: &Name, index: usize, position: Position) -> Position {
    use Position::*;
    if position == Raw || raw_node(kind) || raw_identifier_slot(kind, index) {
        return Raw;
    }
    if position == Binders {
        return Binder;
    }
    if position == FieldPayload {
        return if index == 0 { Binders } else { Term };
    }
    if (["app", "proj", "pipeProj"]
        .iter()
        .any(|leaf| kind_is(kind, "Term", leaf))
        && index == 0)
        || (kind_is(kind, "Term", "explicit") && index == 1)
    {
        // Lean's elabAppFn resolves an identifier head directly. Parentheses
        // and other term heads go through term elaboration and do run macros.
        return AppHead;
    }
    if [
        "explicitBinder",
        "implicitBinder",
        "strictImplicitBinder",
        "instBinder",
    ]
    .iter()
    .any(|leaf| kind_is(kind, "Term", leaf))
    {
        return if index == 2 || (index == 3 && kind_is(kind, "Term", "explicitBinder")) {
            Term
        } else {
            Raw
        };
    }
    if position == Binder {
        if kind_is(kind, "Term", "typeAscription") {
            return if index == 3 { Term } else { Raw };
        }
        if kind_is(kind, "Term", "paren") || kind == &Name::from_components(["null"]) {
            return Binder;
        }
        // A pattern binder's components remain patterns, rather than binder
        // declarations. Literal and constructor macros are meaningful there.
        return Term;
    }
    if (kind_is(kind, "Term", "basicFun") && index == 0)
        || (kind_is(kind, "Term", "forall") && index == 1)
        || (["declSig", "optDeclSig"]
            .iter()
            .any(|leaf| kind_is(kind, "Command", leaf))
            && index == 0)
        || (["letIdDecl", "letEqnsDecl", "letPatDecl"]
            .iter()
            .any(|leaf| kind_is(kind, "Term", leaf))
            && index == 1)
        || (kind_is(kind, "Tactic", "intro") && index == 1)
        || (*kind == Name::from_components(["tacticFunext___"]) && index == 1)
    {
        return Binders;
    }
    if kind_is(kind, "Term", "depArrow") && index == 0 {
        return Binder;
    }
    if kind_is(kind, "Term", "structInstField") && index == 1 {
        return FieldPayload;
    }
    if (kind_is(kind, "Term", "explicitUniv") && index != 0)
        || (kind_is(kind, "Term", "matchDiscr") && index == 0)
        || (kind_is(kind, "Term", "namedPattern") && index == 0)
        || (kind_is(kind, "Term", "set_option") && (index == 1 || index == 2))
        || (kind_is(kind, "Term", "open") && index == 1)
        || (kind_is(kind, "Term", "doIdDecl") && index == 0)
        || (kind_is(kind, "Tactic", "rename") && index == 3)
        || (kind_is(kind, "Tactic", "injection") && index != 1)
        || (kind_is(kind, "Tactic", "set_option") && (index == 1 || index == 3))
        || (kind_is(kind, "Tactic", "open") && index == 1)
        || (kind_is(kind, "Tactic", "induction") && index == 3)
        || (kind_is(kind, "Tactic", "funInduction") && index == 2)
        || (*kind == Name::from_components(["tacticBy_cases_:_"]) && index == 1)
        || (kind_is(kind, "Command", "ctor") && index < 4)
        || (kind_is(kind, "Command", "structSimpleBinder") && index < 2)
        || ([
            "structExplicitBinder",
            "structImplicitBinder",
            "structInstBinder",
        ]
        .iter()
        .any(|leaf| kind_is(kind, "Command", leaf))
            && index < 3)
    {
        return Raw;
    }
    Term
}
