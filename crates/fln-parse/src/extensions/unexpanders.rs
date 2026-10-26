//! The app unexpanders the pin derives from a file's notations, as data a printer applies
//! (`mkUnexpander`, vendored `Lean/Elab/Notation.lean:103-128`).
//!
//! `notation … => c a₁ … aₙ`, and every mixfix (an `infixl` is the notation
//! `lhs " op " rhs => f lhs rhs`), declares an `app_unexpander` for `c` when `c` names exactly one
//! global and no variable occurs twice among the `aᵢ`. It rewrites `c a₁ … aₙ` (as delaborated
//! syntax) to the notation's own items. A `macro` or `macro_rules` declares none.
//!
//! What is recorded here is the notation's head constant, its arity, its precedence and its
//! items, each item an atom or the place the `k`-th argument goes. An `aᵢ` other than a variable
//! (a literal, a nested application) makes the pin's pattern match only some delaborated
//! arguments; this module does not decide which, so such a notation is recorded with no items
//! and a printer refuses a term it might apply to.
use super::*;

/// One item of a notation as it prints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnexpanderItem {
    /// An atom, as declared: its leading spaces print as written, a trailing space is a line.
    Atom(String),
    /// The right-hand side's `position`-th argument, bracketed below `precedence`.
    Argument { position: usize, precedence: u32 },
}

/// The notations a printer applies at one command: their unexpanders, newest first, and the
/// active tokens that decide whether two of its tokens written together would lex as one (the
/// pin's formatter separates those, `pushToken`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Notations {
    pub unexpanders: Vec<Unexpander>,
    /// Every active token of more than one character that begins with a symbol character.
    pub tokens: Vec<String>,
}

/// An application of `head` to at least `arity` explicit arguments prints as `items`, the first
/// `arity` of them in its argument places and any others applied after it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unexpander {
    pub head: Name,
    pub arity: usize,
    /// The notation's precedence: below it, the printed notation is bracketed.
    pub precedence: u32,
    /// `None` when the pin's unexpander exists but its pattern is not one this module reads.
    pub items: Option<Vec<UnexpanderItem>>,
}

impl FileGrammar {
    /// The notations active here, with the tokens their layout reads; empty without any.
    pub fn notations(&self) -> Notations {
        let unexpanders = self.unexpanders();
        if unexpanders.is_empty() {
            return Notations::default();
        }
        let grammar = self.grammar();
        let tokens = grammar
            .table
            .tokens()
            .into_iter()
            .filter(|token| {
                token.chars().count() > 1
                    && token
                        .chars()
                        .next()
                        .is_some_and(|first| !fln_syntax::token::is_id_first(first))
            })
            .map(str::to_owned)
            .collect();
        Notations {
            unexpanders,
            tokens,
        }
    }

    /// The unexpanders of the notations active here, newest first (the order of
    /// `appUnexpanderAttribute.getValues`). A notation whose template is not yet resolved to
    /// its globals declares none here.
    pub fn unexpanders(&self) -> Vec<Unexpander> {
        let rules = self.active_rules(&self.top().trail);
        if rules.is_empty() {
            return Vec::new();
        }
        // A `local` notation is gone after its section, a `scoped` one outside its namespace:
        // only syntax the current grammar reads prints.
        let grammar = self.grammar();
        let declared = self
            .declared
            .iter()
            .rev()
            .chain(self.native_scoped.values().flatten())
            .chain(self.native_imported.iter());
        let mut found = Vec::new();
        for decl in declared {
            if !grammar.kinds.contains(&decl.decl) {
                continue;
            }
            let Some(rule) = rules.get(&decl.decl) else {
                continue;
            };
            let Some(case) = rule
                .cases()
                .find(|case| case.prechecked && case.pattern.is_none() && case.source.is_some())
            else {
                continue;
            };
            if let Some(unexpander) = derive(decl, case) {
                found.push(unexpander);
            }
        }
        found
    }
}

/// `mkUnexpander` for one notation clause, `None` where the pin derives none.
fn derive(decl: &SyntaxDecl, case: &NotationRule) -> Option<Unexpander> {
    let (head, arguments) = match &case.rhs {
        head @ Syntax::Ident { .. } => (head, &[][..]),
        Syntax::Node { kind, args, .. }
            if *kind == Name::from_components(["Lean", "Parser", "Term", "app"]) =>
        {
            let [head @ Syntax::Ident { .. }, arguments] = args.as_slice() else {
                return None;
            };
            (head, null_args(arguments)?)
        }
        _ => return None,
    };
    // Templates retain their written identifiers so later macro rules can
    // match them. Definition-site identity lives in pre-resolution metadata;
    // only the final expansion anchors the spelling under `_root_`.
    let Syntax::Ident { preresolved, .. } = head else {
        return None;
    };
    let [Preresolved::Decl { name: head, fields }] = preresolved.as_slice() else {
        return None;
    };
    if head.is_anonymous() || !fields.is_empty() {
        return None;
    }
    let variables: Vec<&Name> = case.variables.iter().map(|(_, name)| name).collect();
    // `hasDuplicateAntiquot`: a variable twice anywhere in the arguments, and no unexpander.
    let mut seen = BTreeSet::new();
    for argument in arguments {
        let mut duplicate = false;
        visit_idents(argument, &mut |name| {
            if variables.contains(&name) && !seen.insert(name.clone()) {
                duplicate = true;
            }
        });
        if duplicate {
            return None;
        }
    }
    let unexpander = |items| Unexpander {
        head: head.clone(),
        arity: arguments.len(),
        precedence: precedence(&decl.descr),
        items,
    };
    // Each argument a variable (`removeParentheses` first), in the order the template takes them.
    let mut positions = BTreeMap::new();
    for (position, argument) in arguments.iter().enumerate() {
        let Syntax::Ident { val, .. } = unparenthesized(argument) else {
            return Some(unexpander(None));
        };
        if !variables.contains(&val) {
            return Some(unexpander(None));
        }
        positions.insert(val.clone(), position);
    }
    Some(unexpander(items(&decl.descr, case, &positions)))
}

fn precedence(descr: &Descr) -> u32 {
    match descr {
        Descr::Node { prec, .. } | Descr::TrailingNode { prec, .. } => *prec,
        _ => MAX_PREC,
    }
}

/// The notation's items by child, each term the argument its variable is passed as.
fn items(
    descr: &Descr,
    case: &NotationRule,
    positions: &BTreeMap<Name, usize>,
) -> Option<Vec<UnexpanderItem>> {
    let mut children = Vec::new();
    match descr {
        Descr::Node { body, .. } => flatten(body, &mut children)?,
        Descr::TrailingNode { lhs_prec, body, .. } => {
            children.push(Child::Term(*lhs_prec));
            flatten(body, &mut children)?;
        }
        _ => return None,
    }
    let mut items = Vec::new();
    for (index, child) in children.into_iter().enumerate() {
        items.push(match child {
            Child::Atom(text) => UnexpanderItem::Atom(text),
            Child::Term(precedence) => {
                let (_, variable) = case
                    .variables
                    .iter()
                    .find(|(path, _)| path.as_slice() == [index])?;
                UnexpanderItem::Argument {
                    position: *positions.get(variable)?,
                    precedence,
                }
            }
        });
    }
    Some(items)
}

enum Child {
    Atom(String),
    Term(u32),
}

/// A notation's body, one child per item; `None` for an item other than an atom or a term.
fn flatten(descr: &Descr, children: &mut Vec<Child>) -> Option<()> {
    match descr {
        Descr::Binary(name, left, right) if *name == Name::from_components(["andthen"]) => {
            flatten(left, children)?;
            flatten(right, children)
        }
        Descr::Symbol(text) | Descr::NonReservedSymbol(text, _) => {
            children.push(Child::Atom(text.clone()));
            Some(())
        }
        Descr::Cat(category, precedence) if *category == Name::from_components(["term"]) => {
            children.push(Child::Term(*precedence));
            Some(())
        }
        _ => None,
    }
}

/// `removeParentheses` at the top of an argument.
fn unparenthesized(syntax: &Syntax) -> &Syntax {
    match syntax {
        Syntax::Node { kind, args, .. }
            if *kind == Name::from_components(["Lean", "Parser", "Term", "paren"])
                && args.len() == 3 =>
        {
            unparenthesized(&args[1])
        }
        _ => syntax,
    }
}

fn visit_idents(syntax: &Syntax, visit: &mut impl FnMut(&Name)) {
    match syntax {
        Syntax::Ident { val, .. } => visit(val),
        Syntax::Node { args, .. } => {
            for arg in args {
                visit_idents(arg, visit);
            }
        }
        _ => {}
    }
}
