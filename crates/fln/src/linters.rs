//! The pin's other default-on warnings that need no elaboration state beyond a command's
//! syntax and its admitted declaration: `linter.deprecated`'s note on `structure … :=`,
//! `class … :=` and `inductive … :=` (`Lean/Elab/Structure.lean:341`,
//! `Lean/Elab/Inductive.lean:88`), and `linter.defProp` (`Lean/Linter/DefProp.lean`).
//! The unused-variables linter has its own module.
use crate::unused_variables::{linter_value, parser_kind};
use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::Syntax;

/// One warning: its byte offset in the command and its text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Lint {
    pub at: usize,
    pub message: String,
}

fn args(syntax: &Syntax) -> &[Syntax] {
    match syntax {
        Syntax::Node { args, .. } => args,
        _ => &[],
    }
}

fn original_pos(syntax: &Syntax) -> Option<usize> {
    match syntax.info() {
        SourceInfo::Original { pos, .. } => Some(pos.0),
        _ => None,
    }
}

fn is_kind(syntax: &Syntax, kind: &[&str]) -> bool {
    syntax.kind() == Some(&parser_kind(kind))
}

/// The pin's note on the old `:=` form of a `structure`, `class` or `inductive`, at the
/// `:=` token. It is logged while the command elaborates, so `sorry` does not suppress it.
pub(crate) fn deprecated_assignment_syntax(command: &Syntax, options: &KVMap) -> Option<Lint> {
    if !linter_value(options, &["linter", "deprecated"]) {
        return None;
    }
    let [_, declaration] = args(command) else {
        return None;
    };
    let (keyword, message) = if is_kind(declaration, &["Command", "structure"]) {
        let command = if is_kind(args(declaration).first()?, &["Command", "classTk"]) {
            "class"
        } else {
            "structure"
        };
        (
            args(args(declaration).get(4)?).first()?,
            format!("`{command} ... :=` has been deprecated in favor of `{command} ... where`."),
        )
    } else if is_kind(declaration, &["Command", "inductive"]) {
        (
            args(args(declaration).get(3)?).first()?,
            "`inductive ... :=` has been deprecated in favor of `inductive ... where`".to_owned(),
        )
    } else {
        return None;
    };
    let Syntax::Atom { val, .. } = keyword else {
        return None;
    };
    (val == ":=").then_some(Lint {
        at: original_pos(keyword)?,
        message: format!(
            "{message}\n\nNote: This linter can be disabled with `set_option linter.deprecated false`"
        ),
    })
}

/// Whether `type_` is a proposition: under its binders, an application of a constant whose
/// type ends in `Prop`, or a bound variable ranging over `Prop`. Anything undecided is not.
fn is_proposition(type_: &Expr) -> bool {
    let mut binders: Vec<&Expr> = Vec::new();
    let mut body = type_;
    loop {
        match body.node() {
            ExprNode::ForallE {
                binder_type,
                body: next,
                ..
            } => {
                binders.push(binder_type);
                body = next;
            }
            ExprNode::MData { expr, .. } => body = expr,
            _ => break,
        }
    }
    let mut head = body;
    while let ExprNode::App { f, .. } = head.node() {
        head = f;
    }
    match head.node() {
        ExprNode::BVar { idx } => usize::try_from(*idx)
            .ok()
            .and_then(|idx| binders.len().checked_sub(idx + 1))
            .is_some_and(|binder| {
                matches!(binders[binder].node(), ExprNode::Sort { level } if level.is_zero())
            }),
        _ => false,
    }
}

/// `linter.defProp`: a `def` (not an `abbrev`) whose type is a proposition, at the command's
/// first token. `env` resolves the constants the type's head names.
pub(crate) fn definition_is_proposition(
    command: &Syntax,
    name: &Name,
    type_: &Expr,
    abbreviation: bool,
    env: &fln_env::environment::Environment,
    options: &KVMap,
) -> Option<Lint> {
    if abbreviation || !linter_value(options, &["linter", "defProp"]) {
        return None;
    }
    let [_, declaration] = args(command) else {
        return None;
    };
    if !is_kind(declaration, &["Command", "definition"]) {
        return None;
    }
    let mut head = type_;
    loop {
        match head.node() {
            ExprNode::ForallE { body, .. } => head = body,
            ExprNode::MData { expr, .. } => head = expr,
            _ => break,
        }
    }
    while let ExprNode::App { f, .. } = head.node() {
        head = f;
    }
    let proposition = match head.node() {
        ExprNode::Const { name, .. } => env
            .find(name)
            .is_some_and(|info| ends_in_prop_type(&info.constant_val().type_)),
        _ => is_proposition(type_),
    };
    if !proposition {
        return None;
    }
    let mut first = None;
    let mut pending = vec![command];
    while let Some(node) = pending.pop() {
        if let Some(at) = original_pos(node) {
            first = Some(first.map_or(at, |first: usize| first.min(at)));
        }
        pending.extend(args(node).iter());
    }
    Some(Lint {
        at: first?,
        message: format!(
            "Definition `{}` is a proposition; use `theorem` instead of `def`\n\nNote: This linter \
             can be disabled with `set_option linter.defProp false`",
            name.to_display_string()
        ),
    })
}

/// Whether a constant's type ends in `Prop`, i.e. its full application is a proposition.
fn ends_in_prop_type(type_: &Expr) -> bool {
    let mut type_ = type_;
    loop {
        match type_.node() {
            ExprNode::ForallE { body, .. } => type_ = body,
            ExprNode::MData { expr, .. } => type_ = expr,
            ExprNode::Sort { level } => return level.is_zero(),
            _ => return false,
        }
    }
}
