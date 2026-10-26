//! The pin's other default-on warnings that need no elaboration state beyond a command's
//! syntax and its admitted declaration: `linter.deprecated`'s note on `structure … :=`,
//! `class … :=` and `inductive … :=` (`Lean/Elab/Structure.lean:341`,
//! `Lean/Elab/Inductive.lean:88`), `linter.defProp` (`Lean/Linter/DefProp.lean`), and the two
//! reducibility warnings a declaration's elaboration logs for an `instance` attribute and a
//! class-typed `def` (`Lean/Meta/Instances.lean:281-289`, `Lean/Elab/MutualDef.lean:1246-1256`).
//! The unused-variables linter has its own module.
use crate::unused_variables::{linter_value, parser_kind};
use fln_core::expr::{Expr, ExprNode};
use fln_core::level::{Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_core::options::KVMap;
use fln_elab::reducibility::Reducibility;
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
    Some(Lint {
        at: first_position(command)?,
        message: format!(
            "Definition `{}` is a proposition; use `theorem` instead of `def`\n\nNote: This linter \
             can be disabled with `set_option linter.defProp false`",
            name.to_display_string()
        ),
    })
}

/// The parameters of `level`, in the order `CollectLevelParams.visitLevel` first meets them
/// (vendored `Lean/Util/CollectLevelParams.lean`): left to right, each once.
fn level_params(level: &Level, params: &mut Vec<Name>) {
    match level.view() {
        LevelView::Succ(inner) => level_params(inner, params),
        LevelView::Max(left, right) | LevelView::IMax(left, right) => {
            level_params(left, params);
            level_params(right, params);
        }
        LevelView::Param(name) => {
            if !params.contains(name) {
                params.push(name.clone());
            }
        }
        LevelView::Zero | LevelView::MVar(_) => {}
    }
}

/// `univParamsGrouped` (vendored `Lean/Linter/CheckUnivs.lean:43-55`): the parameters of every
/// level in `type_`, a `Sort`'s or a constant's universe argument, one group per level, skipping
/// `name`'s own `proof_*` auxiliaries. Distinct groups, in first-seen order.
fn level_groups(type_: &Expr, name: &Name) -> Vec<Vec<Name>> {
    let mut groups: Vec<Vec<Name>> = Vec::new();
    let mut insert = |level: &Level| {
        let mut params = Vec::new();
        level_params(level, &mut params);
        if !groups.contains(&params) {
            groups.push(params);
        }
    };
    let mut visited = std::collections::HashSet::new();
    let mut pending = vec![type_];
    while let Some(expr) = pending.pop() {
        if !visited.insert(expr) {
            continue;
        }
        match expr.node() {
            ExprNode::Sort { level } => insert(level),
            ExprNode::Const {
                name: constant,
                levels,
            } => {
                let auxiliary = constant.parent() == *name
                    && matches!(constant.leaf_view(), LeafView::Str(leaf) if leaf.starts_with("proof_"));
                if !auxiliary {
                    levels.iter().for_each(&mut insert);
                }
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    groups
}

/// `badParams` (vendored `Lean/Linter/CheckUnivs.lean:57-69`): a parameter is good where a group
/// holds it alone, or (recursively) only beside good ones; the rest of the groups' parameters are
/// bad, flattened in group order. The pin keeps the groups in a hash set, so their order is the
/// set's: `None` where two orders of the groups would print the bad parameters differently.
fn bad_params(mut groups: Vec<Vec<Name>>) -> Option<Vec<Name>> {
    loop {
        let good: Vec<Name> = groups
            .iter()
            .filter_map(|group| match group.as_slice() {
                [only] => Some(only.clone()),
                _ => None,
            })
            .collect();
        if good.is_empty() {
            break;
        }
        for group in &mut groups {
            group.retain(|param| !good.contains(param));
        }
    }
    let flatten = |groups: &[&Vec<Name>]| {
        let mut bad: Vec<Name> = Vec::new();
        for param in groups.iter().flat_map(|group| group.iter()) {
            if !bad.contains(param) {
                bad.push(param.clone());
            }
        }
        bad
    };
    let remaining: Vec<&Vec<Name>> = groups.iter().filter(|group| !group.is_empty()).collect();
    let bad = flatten(&remaining);
    // Every order of the remaining groups must flatten alike. Two groups are compared in both
    // orders; more than two that are not all one order of the same parameters are refused.
    let unordered = match remaining.as_slice() {
        [] | [_] => false,
        [first, second] => flatten(&[second, first]) != bad,
        _ => remaining.iter().any(|group| **group != bad),
    };
    (!unordered).then_some(bad)
}

/// `linter.checkUnivs` (vendored `Lean/Linter/CheckUnivs.lean:71-87`): a declaration whose type
/// has universe parameters that occur only together, never alone, warns at the command. `Err`
/// where the pin's message depends on what this door does not reproduce: the order of its hash
/// set (`bad_params`) or a private name's displayed form.
pub(crate) fn universes_only_together(
    command: &Syntax,
    name: &Name,
    type_: &Expr,
    options: &KVMap,
) -> Result<Option<Lint>, &'static str> {
    if !linter_value(options, &["linter", "checkUnivs"]) {
        return Ok(None);
    }
    let Some(bad) = bad_params(level_groups(type_, name)) else {
        return Err("`linter.checkUnivs` over levels the pin orders by its hash set");
    };
    if bad.is_empty() {
        return Ok(None);
    }
    if crate::pretty::is_private(name) {
        return Err("`linter.checkUnivs` for a private declaration");
    }
    let universes = bad
        .iter()
        .map(|param| format!("`{}`", param.to_display_string()))
        .collect::<Vec<_>>()
        .join(", ");
    let Some(at) = first_position(command) else {
        return Ok(None);
    };
    Ok(Some(Lint {
        at,
        message: format!(
            "`{}`: universes {universes} only occur together. This usually means there is a \
             `max` expression in the type where none of these universes appear on their own.\n\n\
             Note: This linter can be disabled with `set_option linter.checkUnivs false`",
            name.to_display_string()
        ),
    }))
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

/// The offset of `syntax`'s first token, where the pin positions a message about it.
fn first_position(syntax: &Syntax) -> Option<usize> {
    let mut first = None;
    let mut pending = vec![syntax];
    while let Some(node) = pending.pop() {
        if let Some(at) = original_pos(node) {
            first = Some(first.map_or(at, |first: usize| first.min(at)));
        }
        pending.extend(args(node).iter());
    }
    first
}

/// The attribute instances of a declaration's own `@[…]` list, in order.
fn attribute_instances(command: &Syntax) -> Vec<&Syntax> {
    let [modifiers, _] = args(command) else {
        return Vec::new();
    };
    match args(modifiers).get(1).and_then(|slot| args(slot).first()) {
        Some(list) if is_kind(list, &["Term", "attributes"]) => args(list)
            .get(1)
            .map_or(&[][..], args)
            .iter()
            .step_by(2)
            .collect(),
        _ => Vec::new(),
    }
}

/// The status a reducibility attribute instance sets, as `fln_elab`'s source scope reads it.
fn reducibility_attribute(attribute: &Syntax) -> Option<Reducibility> {
    let [_, attribute] = args(attribute) else {
        return None;
    };
    if !is_kind(attribute, &["Attr", "simple"]) {
        return None;
    }
    let Some(Syntax::Ident { val, .. }) = args(attribute).first() else {
        return None;
    };
    Some(match val.to_display_string().as_str() {
        "reducible" => Reducibility::Reducible,
        "irreducible" => Reducibility::Irreducible,
        "semireducible" => Reducibility::Semireducible,
        "implicit_reducible" | "instance_reducible" => Reducibility::ImplicitReducible,
        _ => return None,
    })
}

/// The offset of an `instance` attribute instance (`instance`, `scoped instance`,
/// `local instance`, with or without a priority), at its `instance` keyword.
fn instance_attribute(attribute: &Syntax) -> Option<usize> {
    let [_, attribute] = args(attribute) else {
        return None;
    };
    is_kind(attribute, &["Attr", "instance"])
        .then(|| first_position(attribute))
        .flatten()
}

/// The pin's text when the `instance` attribute is added to `name`, a definition that is
/// neither `@[reducible]` nor `@[implicit_reducible]` (`Lean/Meta/Instances.lean:288`).
pub(crate) fn unmarked_instance_message(name: &Name) -> String {
    format!(
        "instance `{}` must be marked with `@[reducible]` or `@[implicit_reducible]`",
        crate::pretty::message_name(name)
    )
}

/// The offsets of the `instance` attributes in a `def`'s or an `abbrev`'s own attribute list
/// that the pin's `addInstance` warns about (`Lean/Meta/Instances.lean:281-289`): attributes
/// apply in list order, so an `instance` before any `@[reducible]` or `@[implicit_reducible]`
/// finds the declaration unmarked. An `abbrev`'s own `reducible` is added after its list
/// (`mkDefViewOfAbbrev`), so it marks nothing in time. The caller decides that the declaration
/// is a definition. An `instance` command marks its declaration `implicitReducible` before its
/// attributes apply, and a `theorem` or an `opaque` is no definition: none of them is read.
pub(crate) fn unmarked_instance_attributes(command: &Syntax) -> Vec<usize> {
    let [_, declaration] = args(command) else {
        return Vec::new();
    };
    if !is_kind(declaration, &["Command", "definition"])
        && !is_kind(declaration, &["Command", "abbrev"])
    {
        return Vec::new();
    }
    let mut status = Reducibility::Semireducible;
    let mut sites = Vec::new();
    for attribute in attribute_instances(command) {
        if let Some(next) = reducibility_attribute(attribute) {
            status = next;
        } else if let Some(at) = instance_attribute(attribute)
            && !status.unfolds_at_instances()
        {
            sites.push(at);
        }
    }
    sites
}

/// `warn.classDefReducibility` (`Lean/Elab/MutualDef.lean:1246-1256`, the option at `:1180`):
/// a `def` (not an `abbrev`, `instance`, `theorem`, `example` or `opaque`) whose type, under its
/// binders and through abbreviations (`isClass?`), is a class, unless the type's own head is
/// `Decidable`, `DecidableEq` or `Setoid`, and whose attributes leave it neither `reducible`,
/// `implicitReducible` nor `irreducible`. It is logged once the command's declarations are
/// elaborated, before its linters run, at the command's first token. `is_class` answers for the
/// class registry.
pub(crate) fn class_definition_reducibility(
    command: &Syntax,
    name: &Name,
    type_: &Expr,
    env: &fln_env::environment::Environment,
    is_class: impl FnOnce(&Name) -> bool,
    options: &KVMap,
) -> Option<Lint> {
    if !options.get_bool(
        &Name::from_components(["warn", "classDefReducibility"]),
        true,
    ) {
        return None;
    }
    let [_, declaration] = args(command) else {
        return None;
    };
    if !is_kind(declaration, &["Command", "definition"]) {
        return None;
    }
    let status = attribute_instances(command)
        .into_iter()
        .filter_map(reducibility_attribute)
        .next_back()
        .unwrap_or(Reducibility::Semireducible);
    if status != Reducibility::Semireducible {
        return None;
    }
    let excluded = fln_elab::instances::result_head(type_).is_some_and(|head| {
        ["Decidable", "DecidableEq", "Setoid"]
            .iter()
            .any(|excluded| head == Name::from_components([*excluded]))
    });
    if excluded {
        return None;
    }
    let (_, class) = fln_elab::instances::instance_telescope(env, type_)?;
    if !is_class(&class) {
        return None;
    }
    Some(Lint {
        at: first_position(command)?,
        message: format!(
            "Definition `{}` of class type must be marked with `@[reducible]` or \
             `@[implicit_reducible]`",
            crate::pretty::message_name(name)
        ),
    })
}

/// The pin's `Linter.checkDeprecated` warning for a use of `constant` (vendored
/// `Lean/Linter/Deprecated.lean:62-92`), named as the use's `scope` names constants: the
/// entry's text, or its replacement with the notes on a different type, a different namespace
/// or a protected replacement. `None` when `constant` is not deprecated in `environment`. A
/// journal that cannot be read, or a type this printer cannot print, is a refusal, never a
/// shorter message.
pub(crate) fn deprecation_message(
    environment: &fln_env::environment::Environment,
    scope: &fln_elab::source::scope::SourceScope,
    constant: &Name,
    kernel: crate::Budget,
) -> Result<Option<String>, &'static str> {
    let deprecations = fln_elab::deprecations::Deprecations::read(environment)
        .map_err(|_| "a readable deprecation journal")?;
    let Some(entry) = deprecations.get(constant) else {
        return Ok(None);
    };
    let mut printer = crate::pretty::Printer::in_scope(environment, scope);
    let mut message = format!("`{}` has been deprecated", printer.full_name(constant));
    let new_name = match (&entry.text, &entry.new_name) {
        (Some(text), _) => {
            message.push_str(": ");
            message.push_str(text);
            return Ok(Some(message));
        }
        (None, None) => return Ok(Some(message)),
        (None, Some(new_name)) => new_name,
    };
    message.push_str(&format!(": Use `{}` instead", printer.full_name(new_name)));
    let (Some(old), Some(new)) = (environment.find(constant), environment.find(new_name)) else {
        return Ok(Some(message));
    };
    let (old_type, new_type) = (&old.constant_val().type_, &new.constant_val().type_);
    if !fln_elab::source::reducibly_same_type(environment, old_type, new_type, kernel) {
        let updated = printer
            .indented(new_type)
            .map_err(|crate::pretty::Unsupported(reason)| reason)?;
        let original = printer
            .indented(old_type)
            .map_err(|crate::pretty::Unsupported(reason)| reason)?;
        message.push_str(&format!(
            "\n\nNote: The updated constant has a different type:{updated}\ninstead of{original}"
        ));
    }
    let (old_prefix, new_prefix) = (constant.parent(), new_name.parent());
    if old_prefix.is_anonymous() {
        return Ok(Some(message));
    }
    // The namespace, then visibility, exclusively and in this order.
    if old_prefix != new_prefix {
        let example = match constant.leaf_view() {
            fln_core::name::LeafView::Str(root) => format!(
                " (e.g., from `x.{root}` to `{} x`)",
                printer.display_name(new_name)
            ),
            _ => String::new(),
        };
        message.push_str(&format!(
            "\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed{example}."
        ));
    } else {
        let protected = fln_elab::protected_names::ProtectedNames::read(environment)
            .map_err(|_| "a readable protected-declaration journal")?;
        if !protected.contains(constant) && protected.contains(new_name) {
            // `componentsRev`: the prefix's last component first.
            let last = match new_prefix.leaf_view() {
                fln_core::name::LeafView::Str(text) => Name::from_components([text]),
                fln_core::name::LeafView::Num(value) => Name::num(Name::anonymous(), value),
                fln_core::name::LeafView::Anonymous => Name::anonymous(),
            };
            let qualifier = if new_prefix.parent().is_anonymous() {
                String::new()
            } else {
                format!(
                    "at least the last component `{}` of ",
                    crate::pretty::message_name(&last)
                )
            };
            message.push_str(&format!(
                "\n\nNote: `{}` is protected. References to this constant must include {qualifier}its prefix `{}` even when inside its namespace.",
                printer.full_name(new_name),
                crate::pretty::message_name(&new_prefix)
            ));
        }
    }
    Ok(Some(message))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(params: &[&str]) -> Vec<Name> {
        params
            .iter()
            .map(|param| Name::from_components([*param]))
            .collect()
    }

    #[test]
    fn bad_params_are_the_pins_bad_params() {
        // `max u v` alone: both bad, in the level's order.
        assert_eq!(
            bad_params(vec![names(&["u", "v"])]),
            Some(names(&["u", "v"]))
        );
        // `u` alone somewhere, so `max u v` is fine (`goodUnivsDominated`).
        assert_eq!(
            bad_params(vec![names(&["u"]), names(&["u", "v"])]),
            Some(Vec::new())
        );
        // Each alone somewhere.
        assert_eq!(
            bad_params(vec![names(&["u"]), names(&["v"]), names(&["u", "v"])]),
            Some(Vec::new())
        );
        // A good parameter is removed, then the rest are judged again.
        assert_eq!(
            bad_params(vec![names(&["u"]), names(&["u", "v", "w"])]),
            Some(names(&["v", "w"]))
        );
        // Levels without parameters (`Sort 0`) contribute nothing.
        assert_eq!(bad_params(vec![Vec::new()]), Some(Vec::new()));
        // Two levels naming the bad parameters in different orders: the pin's hash set decides.
        assert_eq!(
            bad_params(vec![names(&["u", "v"]), names(&["v", "u"])]),
            None
        );
    }

    #[test]
    fn level_groups_read_sorts_and_constant_levels_but_not_proof_auxiliaries() {
        let max = Level::max(
            Level::param(Name::from_components(["u"])),
            Level::param(Name::from_components(["v"])),
        )
        .unwrap();
        let sort = Expr::sort(max.clone());
        let name = Name::from_components(["f"]);
        assert_eq!(level_groups(&sort, &name), vec![names(&["u", "v"])]);
        let auxiliary = Expr::const_(Name::str(name.clone(), "proof_1"), vec![max.clone()]);
        assert_eq!(level_groups(&auxiliary, &name), Vec::<Vec<Name>>::new());
        let other = Expr::const_(Name::from_components(["g"]), vec![max]);
        assert_eq!(level_groups(&other, &name), vec![names(&["u", "v"])]);
    }
}
