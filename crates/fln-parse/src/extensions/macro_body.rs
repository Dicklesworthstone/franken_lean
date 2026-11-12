//! Compile pure MacroM syntax construction to the existing hygienic templates.
//!
//! Quotations read the current scope; they do not allocate another one
//! (`Lean.Elab.Quotation.mkSyntaxQuotation`). Immutable aliases and monadic
//! binds can therefore compose their templates before the ordinary expansion
//! applies that scope. Keep raw syntax and MacroM syntax distinct: `return q`
//! is valid for a bound syntax value, but not for an unevaluated quotation.
//! Arbitrary calls, state changes, control flow, and mutable locals refuse.

use super::*;
use quotation::capture_kinds::{self, CaptureKind};

const UNSUPPORTED: &str = "a macro body outside pure syntax construction";
const TYPE_MISMATCH: &str = "a macro syntax construction with incompatible value types";

struct Value {
    template: Syntax,
    family: CaptureKind,
    category: Option<Name>,
    monadic: bool,
}

struct Compiler<'a> {
    bound: BTreeMap<Name, Value>,
    is_pure: &'a dyn Fn(&Name) -> bool,
    visited: usize,
}

fn item_category(item: &StxItem) -> Option<Name> {
    match item {
        StxItem::Cat(name, _) => Some(name.clone()),
        StxItem::Paren(items) if items.len() == 1 => item_category(&items[0]),
        StxItem::Unary(name, items)
            if simple(name).as_deref() == Some("withPosition") && items.len() == 1 =>
        {
            item_category(&items[0])
        }
        _ => None,
    }
}

fn antiquotation_category(syntax: &Syntax) -> Option<Name> {
    antiquotation_name(syntax)?;
    let mut category = syntax.kind()?.parent();
    if category.leaf_view() == LeafView::Str("pseudo") {
        category = category.parent();
    }
    Some(category)
}

fn pattern_category(children: &[Syntax], path: &[usize]) -> Option<Name> {
    let (first, rest) = path.split_first()?;
    let mut syntax = children.get(*first)?;
    for index in rest {
        syntax = node_args(syntax)?.get(*index)?;
    }
    antiquotation_category(syntax)
}

// The scalar coercions used here are declared in Init/Meta/Defs.lean.
// No coercion from an Option, TSyntaxArray, or TSepArray produces TSyntax.
fn compatible(actual: &Name, expected: &Name) -> bool {
    actual == expected
        || (*expected == Name::from_components(["term"])
            && ["ident", "num", "str", "char", "name", "scientific"]
                .into_iter()
                .any(|kind| *actual == Name::from_components([kind])))
        || (*actual == Name::from_components(["num"])
            && ["prec", "prio"]
                .into_iter()
                .any(|kind| *expected == Name::from_components([kind])))
}

pub(super) fn direct(
    rhs: &Syntax,
    category: &Name,
    variables: &[(Vec<usize>, Name)],
    items: &[StxItem],
    is_pure: &dyn Fn(&Name) -> bool,
) -> Result<Syntax, &'static str> {
    // Preserve the established direct-quotation path and its exact budget.
    if let Some((actual, contents)) = quotation_contents(rhs) {
        if actual != *category {
            return Err("a macro whose right-hand side is not a quotation of its category");
        }
        return quotation::templates::checked(contents, variables);
    }
    let mut compiler = Compiler::new(is_pure);
    for (path, name) in variables {
        let [index] = path.as_slice() else {
            return Err(TYPE_MISMATCH);
        };
        let item = items.get(*index).ok_or(TYPE_MISMATCH)?;
        let family = capture_kinds::item_kind(item, &mut compiler.visited, 0)?;
        compiler.capture(name, family, item_category(item))?;
    }
    compiler.finish(rhs, Some(category))
}

/// A `macro_rules` function returns raw Syntax, so its result need not have
/// the input category. Sequence and optional values are still not Syntax.
pub(super) fn rule(
    rhs: &Syntax,
    variables: &[(Vec<usize>, Name)],
    children: &[Syntax],
    is_pure: &dyn Fn(&Name) -> bool,
) -> Result<Syntax, &'static str> {
    if let Some((_, contents)) = quotation_contents(rhs) {
        return quotation::templates::checked(contents, variables);
    }
    let mut compiler = Compiler::new(is_pure);
    for (path, name) in variables {
        let family = capture_kinds::pattern_kind(children, path, &mut compiler.visited)?;
        compiler.capture(name, family, pattern_category(children, path))?;
    }
    compiler.finish(rhs, None)
}

impl<'a> Compiler<'a> {
    fn new(is_pure: &'a dyn Fn(&Name) -> bool) -> Self {
        Self {
            bound: BTreeMap::new(),
            is_pure,
            visited: 0,
        }
    }

    fn charge(&mut self, depth: usize) -> Result<(), &'static str> {
        if depth > MAX_DESCR_DEPTH {
            return Err("a quoted macro pattern past the node or depth budget");
        }
        quotation::templates::charge(&mut self.visited)
    }

    fn capture(
        &mut self,
        name: &Name,
        family: CaptureKind,
        category: Option<Name>,
    ) -> Result<(), &'static str> {
        self.charge(0)?;
        let value = Value {
            template: synthetic_ident(name.clone()),
            family,
            category,
            monadic: false,
        };
        if self.bound.insert(name.clone(), value).is_some() {
            return Err(TYPE_MISMATCH);
        }
        Ok(())
    }

    fn finish(&mut self, rhs: &Syntax, expected: Option<&Name>) -> Result<Syntax, &'static str> {
        let value = self.eval(rhs, 0)?;
        if !value.monadic
            || value.family != CaptureKind::Scalar
            || expected.is_some_and(|expected| {
                value
                    .category
                    .as_ref()
                    .is_none_or(|actual| !compatible(actual, expected))
            })
        {
            return Err(TYPE_MISMATCH);
        }
        Ok(value.template)
    }

    fn quote(&mut self, category: Name, contents: &Syntax) -> Result<Value, &'static str> {
        self.validate_quotation(contents, 0)?;
        let variables: Vec<_> = self
            .bound
            .keys()
            .map(|name| (vec![], name.clone()))
            .collect();
        let checked = quotation::templates::checked(contents, &variables)?;
        let template = self.substitute(&checked, 0)?;
        Ok(Value {
            template,
            family: CaptureKind::Scalar,
            category: Some(category),
            monadic: true,
        })
    }

    fn validate_quotation(&mut self, syntax: &Syntax, depth: usize) -> Result<(), &'static str> {
        self.charge(depth)?;
        // Sequence families are checked after alias substitution against the
        // original capture paths by capture_kinds::{direct, pattern}.
        if quotation::templates::is_repetition(syntax)? {
            return Ok(());
        }
        if let Some(name) = antiquotation_name(syntax) {
            let value = self.bound.get(&macro_variable(&name)).ok_or(UNSUPPORTED)?;
            let expected = antiquotation_category(syntax).ok_or(TYPE_MISMATCH)?;
            if value.monadic
                || value.family != CaptureKind::Scalar
                || value
                    .category
                    .as_ref()
                    .is_none_or(|actual| !compatible(actual, &expected))
            {
                return Err(TYPE_MISMATCH);
            }
            return Ok(());
        }
        if let Syntax::Node { args, .. } = syntax {
            for child in args {
                self.validate_quotation(child, depth + 1)?;
            }
        }
        Ok(())
    }

    fn substitute(&mut self, syntax: &Syntax, depth: usize) -> Result<Syntax, &'static str> {
        self.charge(depth)?;
        if let Syntax::Ident { val, .. } = syntax
            && let Some(value) = self.bound.get(val)
        {
            if value.monadic {
                return Err(TYPE_MISMATCH);
            }
            return quotation::templates::copy_capture(&value.template, &mut self.visited);
        }
        if let Syntax::Node { info, kind, args } = syntax {
            let mut children = Vec::new();
            for child in args {
                children.push(self.substitute(child, depth + 1)?);
            }
            return Ok(Syntax::Node {
                info: *info,
                kind: kind.clone(),
                args: children,
            });
        }
        Ok(syntax.clone())
    }

    fn eval(&mut self, syntax: &Syntax, depth: usize) -> Result<Value, &'static str> {
        self.charge(depth)?;
        if let Some((category, contents)) = quotation_contents(syntax) {
            return self.quote(category, contents);
        }
        if let Some(name) = ident_name(syntax) {
            let value = self.bound.get(&macro_variable(&name)).ok_or(UNSUPPORTED)?;
            return Ok(Value {
                template: quotation::templates::copy_capture(&value.template, &mut self.visited)?,
                family: value.family.clone(),
                category: value.category.clone(),
                monadic: value.monadic,
            });
        }
        let args = node_args(syntax).ok_or(UNSUPPORTED)?;
        if kind_is(syntax, &["Lean", "Parser", "Term", "paren"]) {
            let [_, body, _] = args else {
                return Err(UNSUPPORTED);
            };
            return self.eval(body, depth + 1);
        }
        if ["termReturn", "doReturn"]
            .into_iter()
            .any(|kind| kind_is(syntax, &["Lean", "Parser", "Term", kind]))
        {
            let [_, body] = args else {
                return Err(UNSUPPORTED);
            };
            let Some([body]) = null_args(body) else {
                return Err(TYPE_MISMATCH);
            };
            return self.pure(body, depth + 1);
        }
        if kind_is(syntax, &["Lean", "Parser", "Term", "app"]) {
            let [function, operands] = args else {
                return Err(UNSUPPORTED);
            };
            let name = ident_name(function).ok_or(UNSUPPORTED)?;
            let Some([operand]) = null_args(operands) else {
                return Err(UNSUPPORTED);
            };
            if self.bound.contains_key(&macro_variable(&name)) || !(self.is_pure)(&name) {
                return Err(UNSUPPORTED);
            }
            return self.pure(operand, depth + 1);
        }
        if ["do", "doNested"]
            .into_iter()
            .any(|kind| kind_is(syntax, &["Lean", "Parser", "Term", kind]))
        {
            let [_, sequence] = args else {
                return Err(UNSUPPORTED);
            };
            return self.sequence(sequence, depth + 1);
        }
        if kind_is(syntax, &["Lean", "Parser", "Term", "doExpr"]) {
            let [expression] = args else {
                return Err(UNSUPPORTED);
            };
            return self.eval(expression, depth + 1);
        }
        if kind_is(syntax, &["Lean", "Parser", "Term", "let"]) {
            let [_, config, declaration, _, body] = args else {
                return Err(UNSUPPORTED);
            };
            empty_config(config)?;
            let (name, rhs) = let_declaration(declaration)?;
            let value = self.eval(rhs, depth + 1)?;
            let key = macro_variable(&name);
            let previous = self.bound.insert(key.clone(), value);
            let result = self.eval(body, depth + 1);
            self.restore(key, previous);
            return result;
        }
        Err(UNSUPPORTED)
    }

    fn pure(&mut self, body: &Syntax, depth: usize) -> Result<Value, &'static str> {
        let mut value = self.eval(body, depth)?;
        if value.monadic || value.family != CaptureKind::Scalar {
            return Err(TYPE_MISMATCH);
        }
        value.monadic = true;
        Ok(value)
    }

    fn restore(&mut self, key: Name, previous: Option<Value>) {
        if let Some(previous) = previous {
            self.bound.insert(key, previous);
        } else {
            self.bound.remove(&key);
        }
    }

    fn sequence(&mut self, sequence: &Syntax, depth: usize) -> Result<Value, &'static str> {
        self.charge(depth)?;
        let args = node_args(sequence).ok_or(UNSUPPORTED)?;
        let items = match args {
            [items] if kind_is(sequence, &["Lean", "Parser", "Term", "doSeqIndent"]) => items,
            [_, items, _] if kind_is(sequence, &["Lean", "Parser", "Term", "doSeqBracketed"]) => {
                items
            }
            _ => return Err(UNSUPPORTED),
        };
        let items = null_args(items).ok_or(UNSUPPORTED)?;
        let mut bindings = Vec::new();
        let result = (|| {
            for (index, item) in items.iter().enumerate() {
                self.charge(depth)?;
                let Some([element, _]) = node_args(item) else {
                    return Err(UNSUPPORTED);
                };
                if !kind_is(item, &["Lean", "Parser", "Term", "doSeqItem"]) {
                    return Err(UNSUPPORTED);
                }
                let binding = if kind_is(element, &["Lean", "Parser", "Term", "doLet"]) {
                    Some(false)
                } else if kind_is(element, &["Lean", "Parser", "Term", "doLetArrow"]) {
                    Some(true)
                } else {
                    None
                };
                if let Some(monadic) = binding {
                    let Some([_, mutable, config, declaration]) = node_args(element) else {
                        return Err(UNSUPPORTED);
                    };
                    if !null_args(mutable).is_some_and(<[Syntax]>::is_empty) {
                        return Err(UNSUPPORTED);
                    }
                    empty_config(config)?;
                    let (name, rhs) = if monadic {
                        let Some([name, annotation, _, rhs]) = node_args(declaration) else {
                            return Err(UNSUPPORTED);
                        };
                        if !kind_is(declaration, &["Lean", "Parser", "Term", "doIdDecl"])
                            || !null_args(annotation).is_some_and(<[Syntax]>::is_empty)
                        {
                            return Err(UNSUPPORTED);
                        }
                        (ident_name(name).ok_or(UNSUPPORTED)?, rhs)
                    } else {
                        let_declaration(declaration)?
                    };
                    let mut value = self.eval(rhs, depth + 1)?;
                    if monadic {
                        if !value.monadic {
                            return Err(TYPE_MISMATCH);
                        }
                        value.monadic = false;
                    }
                    let key = macro_variable(&name);
                    let previous = self.bound.insert(key.clone(), value);
                    bindings.push((key, previous));
                    continue;
                }
                let value = self.eval(element, depth + 1)?;
                if !value.monadic {
                    return Err(TYPE_MISMATCH);
                }
                if index + 1 == items.len() {
                    return Ok(value);
                }
                // A quotation/pure expression has no mutation to discard.
                // Returning before the last element is not such an action.
                if kind_is(element, &["Lean", "Parser", "Term", "doReturn"]) {
                    return Err(UNSUPPORTED);
                }
            }
            Err(TYPE_MISMATCH)
        })();
        for (key, previous) in bindings.into_iter().rev() {
            self.restore(key, previous);
        }
        result
    }
}

fn empty_config(config: &Syntax) -> Result<(), &'static str> {
    if kind_is(config, &["Lean", "Parser", "Term", "letConfig"])
        && node_args(config).is_some_and(|args| {
            matches!(args, [entries] if null_args(entries).is_some_and(<[Syntax]>::is_empty))
        })
    {
        Ok(())
    } else {
        Err(UNSUPPORTED)
    }
}

fn let_declaration(declaration: &Syntax) -> Result<(Name, &Syntax), &'static str> {
    if !kind_is(declaration, &["Lean", "Parser", "Term", "letDecl"]) {
        return Err(UNSUPPORTED);
    }
    let Some([declaration]) = node_args(declaration) else {
        return Err(UNSUPPORTED);
    };
    let Some([binder, binders, annotation, _, rhs]) = node_args(declaration) else {
        return Err(UNSUPPORTED);
    };
    if !kind_is(declaration, &["Lean", "Parser", "Term", "letIdDecl"])
        || !null_args(binders).is_some_and(<[Syntax]>::is_empty)
        || !null_args(annotation).is_some_and(<[Syntax]>::is_empty)
        || !kind_is(binder, &["Lean", "Parser", "Term", "letId"])
    {
        return Err(UNSUPPORTED);
    }
    let Some([name]) = node_args(binder) else {
        return Err(UNSUPPORTED);
    };
    Ok((ident_name(name).ok_or(UNSUPPORTED)?, rhs))
}
