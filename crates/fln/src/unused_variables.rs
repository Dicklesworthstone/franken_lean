//! The pin's unused-variables linter (`Lean/Linter/UnusedVariables.lean`), for a
//! declaration's own signature binders (bead `fln-default-linters-unused-variables-mtnt`).
//!
//! The pin decides use from its info tree: a binder is used when some elaborated
//! identifier refers to it, or when its free variable occurs in the declaration body
//! instantiated before abstraction. This module reads the command's syntax and its
//! admitted declaration instead. A signature binder counts as used when an identifier
//! with its name appears anywhere else in the command, or when its bound variable occurs
//! in the admitted type after it or in the admitted value. Both over-approximate the
//! pin's uses: a shadowing inner binder of the same name counts, and so does any
//! elaborated occurrence. So a warning printed here is one the pin prints too.
//!
//! A body holding a tactic block or `‹_›` is read as the pin reads it with
//! `linter.unusedVariables.analyzeTactics` off: the body's syntax is ignored, and a
//! signature binder is used only when the signature's syntax refers to it or its variable
//! occurs in the admitted type or the final term. This engine's tactics must then reach a
//! term with the same variable occurrences as the pin's, which the stratum measures.
//!
//! A command this increment cannot decide is not linted, exactly as before this
//! module existed: the pin's warning is missing, never invented. That covers `sorry`
//! (the pin skips the whole command); a tactic body of a recursive declaration or one with
//! `where` helpers; every local binder whose scope holds a tactic block; and every binder
//! form other than those read here.
use fln_core::expr::{Expr, ExprNode};
use fln_core::name::{LeafView, Name};
use fln_core::options::KVMap;
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::Syntax;
use std::collections::HashSet;

/// A parser node kind, `Lean.Parser.<components>`.
pub(crate) fn parser_kind(components: &[&str]) -> Name {
    components.iter().fold(
        Name::from_components(["Lean", "Parser"]),
        |name, component| Name::str(name, *component),
    )
}

/// One unused signature binder: its name and its byte offset in the command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnusedBinder {
    pub at: usize,
    pub name: Name,
}

/// The pin's `logLint` text for `linter.unusedVariables`
/// (`Lean/Linter/UnusedVariables.lean`, `Lean/Linter/Util.lean`).
pub(crate) fn message(name: &Name) -> String {
    format!(
        "Variable name `{}` is not explicitly referenced.\n\nThe binding can be removed \
         (if unused) or named `_` (if used implicitly).\n\nNote: This linter can be disabled \
         with `set_option linter.unusedVariables false`",
        name.to_display_string()
    )
}

fn option(options: &KVMap, key: &[&str]) -> Option<bool> {
    let key = Name::from_components(key.iter().copied());
    let on = options.get_bool(&key, true);
    (on == options.get_bool(&key, false)).then_some(on)
}

/// `getLinterValue`: a linter option left unset falls back to `linter.all`, then to `true`,
/// the default of every linter read here.
pub(crate) fn linter_value(options: &KVMap, name: &[&str]) -> bool {
    option(options, name).unwrap_or_else(|| option(options, &["linter", "all"]).unwrap_or(true))
}

/// `getLinterValue linter.unusedVariables` and one of its refinements (`funArgs`,
/// `patternVars`): an unset option falls back to `linter.all`, then to its default `true`.
fn linted(options: &KVMap, refinement: Option<&str>) -> bool {
    let all = option(options, &["linter", "all"]).unwrap_or(true);
    let enabled = option(options, &["linter", "unusedVariables"]).unwrap_or(all);
    enabled
        && refinement.is_none_or(|refinement| {
            option(options, &["linter", "unusedVariables", refinement]).unwrap_or(enabled)
        })
}

fn is_kind(syntax: &Syntax, kind: &[&str]) -> bool {
    syntax.kind() == Some(&parser_kind(kind))
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

/// Every node and leaf of `syntax`, iteratively.
fn walk<'a>(syntax: &'a Syntax, mut visit: impl FnMut(&'a Syntax) -> bool) -> bool {
    let mut pending = vec![syntax];
    while let Some(node) = pending.pop() {
        if visit(node) {
            return true;
        }
        pending.extend(args(node).iter());
    }
    false
}

/// `#reduce`, `syntax (name := reduceCmd) "#reduce" reduceConfig term : command` in namespace
/// `Lean` (vendored `Init/Notation.lean:766`).
pub(crate) fn is_reduce(command: &Syntax) -> bool {
    command.kind() == Some(&Name::from_components(["Lean", "reduceCmd"]))
}

/// The pin's `hasSorry` test (vendored `Lean/Linter/UnusedVariables.lean:471-475`): a command
/// whose syntax holds a `sorry` term or tactic, or `admit`, is not linted.
pub(crate) fn has_sorry(command: &Syntax) -> bool {
    contains_atom(command, &["sorry", "admit"])
}

/// Whether a structure instance in `command` leaves out a field whose default is a proof, and
/// `value` builds that structure. A field `h : P := by tac` is the pin's `autoParam`, filled by
/// running its tactic while the body elaborates, so the pin then reads the body only through
/// its elaborated term ([`runs_tactics`]). Read conservatively: any default whose type is a
/// proposition counts, a tactic's or not, which can only withhold a warning.
pub(crate) fn omits_tactic_field(
    command: &Syntax,
    value: &Expr,
    env: &fln_env::environment::Environment,
) -> bool {
    use fln_env::constants::ConstantInfo;
    let mut instances: Vec<HashSet<Name>> = Vec::new();
    walk(command, |node| {
        if is_kind(node, &["Term", "structInst"]) {
            let mut fields = HashSet::new();
            walk(node, |field| {
                if is_kind(field, &["Term", "structInstField"])
                    && let Some(Syntax::Ident { val, .. }) =
                        args(field).first().and_then(|lval| args(lval).first())
                {
                    fields.insert(root(val));
                }
                false
            });
            instances.push(fields);
        }
        false
    });
    if instances.is_empty() {
        return false;
    }
    let mut pending = vec![value];
    let mut seen = HashSet::new();
    while let Some(expr) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(expr.node())) {
            continue;
        }
        if let ExprNode::Const { name, .. } = expr.node()
            && let Some(ConstantInfo::Ctor(ctor)) = env.find(name)
        {
            let mut type_ = &ctor.base.type_;
            for index in 0..(ctor.num_params + ctor.num_fields) {
                let ExprNode::ForallE {
                    binder_name, body, ..
                } = type_.node()
                else {
                    break;
                };
                let default = Name::str(ctor.induct.append_core(binder_name), "_default");
                if index >= ctor.num_params
                    && env
                        .find(&default)
                        .is_some_and(|info| proof_type(&info.constant_val().type_, env))
                    && instances
                        .iter()
                        .any(|fields| !fields.contains(&root(binder_name)))
                {
                    return true;
                }
                type_ = body;
            }
        }
        match expr.node() {
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
            _ => {}
        }
    }
    false
}

/// Whether `type_`, under its binders, is an application of a constant whose type ends in `Prop`.
fn proof_type(type_: &Expr, env: &fln_env::environment::Environment) -> bool {
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
    let ExprNode::Const { name, .. } = head.node() else {
        return false;
    };
    env.find(name).is_some_and(|info| {
        let mut sort = &info.constant_val().type_;
        loop {
            match sort.node() {
                ExprNode::ForallE { body, .. } => sort = body,
                ExprNode::MData { expr, .. } => sort = expr,
                ExprNode::Sort { level } => return level.is_zero(),
                _ => return false,
            }
        }
    })
}

/// Whether elaborating `syntax` runs a tactic: a tactic block, `‹_›`, or `xs[i]` with no proof
/// given, whose `getElem` argument is the auto-parameter `by get_elem_tactic`. With
/// `linter.unusedVariables.analyzeTactics` off the pin then reads such a body only through its
/// elaborated term (vendored `Lean/Linter/UnusedVariables.lean:396-413`).
fn runs_tactics(syntax: &Syntax) -> bool {
    contains_atom(syntax, &["by", "‹"])
        || walk(syntax, |node| {
            node.kind() == Some(&Name::from_components(["term__[_]"]))
        })
}

fn contains_atom(syntax: &Syntax, atoms: &[&str]) -> bool {
    walk(
        syntax,
        |node| matches!(node, Syntax::Atom { val, .. } if atoms.contains(&val.as_str())),
    )
}

fn root(name: &Name) -> Name {
    let mut current = name.clone();
    while !current.parent().is_anonymous() {
        current = current.parent();
    }
    current
}

/// Whether an identifier in `scope`, other than the binder at `at` itself, may refer to
/// `name`. A named argument's name (`f (y := 5)`) names a parameter of `f`, never a local, so
/// it is not one. Nor is a structure instance's field name given a value (`{ x := 3 }`); a
/// field abbreviation (`{ x }`) is `x := x`, which reads the local.
///
/// A `do` element binding the same name (`let s ← e`) shadows it in the elements after it,
/// which therefore read the new binding; its own value is still read before it binds.
fn referenced(scope: &Syntax, name: &Name, at: usize) -> bool {
    referenced_except(scope, name, &[at])
}

fn referenced_except(scope: &Syntax, name: &Name, binders: &[usize]) -> bool {
    let mut pending = vec![scope];
    while let Some(node) = pending.pop() {
        match node {
            Syntax::Ident { val, .. } => {
                if root(val) == *name
                    && original_pos(node).is_none_or(|pos| !binders.contains(&pos))
                {
                    return true;
                }
            }
            Syntax::Node { .. }
                if is_kind(node, &["Term", "doSeqIndent"])
                    || is_kind(node, &["Term", "doSeqBracketed"]) =>
            {
                let bracketed = usize::from(is_kind(node, &["Term", "doSeqBracketed"]));
                let Some(items) = args(node).get(bracketed).map(args) else {
                    continue;
                };
                for item in items {
                    match args(item).first().and_then(do_binding) {
                        Some((bound, pos)) if bound == *name => {
                            let mut inner = binders.to_vec();
                            inner.push(pos);
                            if referenced_except(item, name, &inner) {
                                return true;
                            }
                            break;
                        }
                        _ => {
                            if referenced_except(item, name, binders) {
                                return true;
                            }
                        }
                    }
                }
                // The brackets of `do { … }` hold no identifier.
            }
            Syntax::Node { args, .. } if is_kind(node, &["Term", "namedArgument"]) => {
                pending.extend(args.iter().skip(2));
            }
            Syntax::Node { args: fields, .. } if is_kind(node, &["Term", "structInstField"]) => {
                let valued = fields.get(1).is_some_and(|rest| !args(rest).is_empty());
                pending.extend(fields.iter().skip(usize::from(valued)));
            }
            Syntax::Node { args, .. } => pending.extend(args.iter()),
            Syntax::Atom { .. } | Syntax::Missing => {}
        }
    }
    false
}

/// One telescope slot per binder the signature declares, named where it names one
/// with original syntax. `None` when the signature has a form this increment does not read.
fn signature_slots(binders: &[Syntax]) -> Option<Vec<Option<(Name, usize)>>> {
    let named = |syntax: &Syntax| match syntax {
        Syntax::Ident { val, .. } => Some(original_pos(syntax).map(|pos| (val.clone(), pos))),
        _ if is_kind(syntax, &["Term", "hole"]) => Some(None),
        _ => None,
    };
    let mut slots = Vec::new();
    for binder in binders {
        if let Some(slot) = named(binder) {
            slots.push(slot);
        } else if is_kind(binder, &["Term", "instBinder"]) {
            slots.push(match args(args(binder).get(1)?) {
                [] => None,
                [name, _colon] => named(name)?,
                _ => return None,
            });
        } else if ["explicitBinder", "implicitBinder", "strictImplicitBinder"]
            .iter()
            .any(|kind| is_kind(binder, &["Term", kind]))
        {
            for name in args(args(binder).get(1)?) {
                slots.push(named(name)?);
            }
        } else {
            return None;
        }
    }
    Some(slots)
}

/// How a declaration's body decides its signature binders' uses.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Body {
    /// No tactic block: an identifier anywhere in the command may use a binder.
    Terms,
    /// A tactic block or `‹_›`: the pin ignores the body's syntax and reads only its final
    /// term (`linter.unusedVariables.analyzeTactics` off), so only the signature's syntax and
    /// the admitted type and value decide.
    Tactics,
}

/// A `def`, `theorem`, `abbrev`, `instance` or `example` whose uses this module can decide:
/// its modifiers, declaration and body regime, or `None`. The pin never lints a command with
/// `sorry`. A tactic body is decided from its proof term, so a recursive declaration (whose
/// admitted term is compiled from the pin's pre-definition differently) or one with `where`
/// helpers is left undecided there.
fn decided(command: &Syntax) -> Option<(&Syntax, &Syntax, Body)> {
    if !is_kind(command, &["Command", "declaration"]) {
        return None;
    }
    let [modifiers, declaration] = args(command) else {
        return None;
    };
    if !["definition", "theorem", "abbrev", "instance", "example"]
        .iter()
        .any(|kind| is_kind(declaration, &["Command", kind]))
        || contains_atom(declaration, &["sorry", "admit"])
    {
        return None;
    }
    if !runs_tactics(declaration) {
        return Some((modifiers, declaration, Body::Terms));
    }
    (!contains_atom(
        declaration,
        &[
            "decreasing_by",
            "termination_by",
            "where",
            "partial_fixpoint",
        ],
    ))
    .then_some((modifiers, declaration, Body::Tactics))
}

/// A `def`, `theorem`, `abbrev`, `instance` or `example` whose term-level binders this module
/// reads: [`decided`]'s, except that a tactic block or `‹_›` leaves only the scopes holding it
/// undecided. A binder outside a tactic block has its whole scope outside it too, so the
/// tactic cannot refer to it; the binders a tactic block holds are never read
/// ([`term_scopes`]). `decreasing_by` is the exception: its proofs are checked in the context
/// of each recursive call, every local around the call in scope, so none is read here.
fn scoped(command: &Syntax) -> Option<&Syntax> {
    // A query's term (`#check`, `#eval`, `#reduce`) is read whole. One that runs a tactic (a
    // block, `‹…›`, or an unproved `xs[i]`) is left undecided: how the pin reads the binders
    // around it there is not measured.
    if ["check", "eval"]
        .iter()
        .any(|kind| is_kind(command, &["Command", kind]))
        || is_reduce(command)
    {
        return (!has_sorry(command) && !runs_tactics(command)).then_some(command);
    }
    if !is_kind(command, &["Command", "declaration"]) {
        return None;
    }
    let [_, declaration] = args(command) else {
        return None;
    };
    (["definition", "theorem", "abbrev", "instance", "example"]
        .iter()
        .any(|kind| is_kind(declaration, &["Command", kind]))
        && !contains_atom(declaration, &["sorry", "admit", "decreasing_by"]))
    .then_some(declaration)
}

/// Whether `node` is a declaration's value: its body, as the pin's `BodyInfo` covers it.
fn is_body(node: &Syntax) -> bool {
    ["declValSimple", "declValEqns", "whereStructInst"]
        .iter()
        .any(|kind| is_kind(node, &["Command", kind]))
}

/// Every node of `command`'s declaration outside tactic blocks for which `select` gives
/// something, when the node holds no tactic block itself ([`scoped`]). A body holding a
/// tactic block anywhere is not read at all: the pin then lints no binder the body
/// introduces, only the signature's (`linter.unusedVariables.analyzeTactics` off).
fn term_scopes<'a, T>(
    command: &'a Syntax,
    mut select: impl FnMut(&'a Syntax) -> Option<T>,
) -> Vec<(&'a Syntax, T)> {
    let mut found = Vec::new();
    let Some(declaration) = scoped(command) else {
        return found;
    };
    let mut pending = vec![declaration];
    while let Some(node) = pending.pop() {
        if is_kind(node, &["Term", "byTactic"])
            || contains_atom_shallow(node, "‹")
            || (is_body(node) && runs_tactics(node))
        {
            continue;
        }
        if let Some(selected) = select(node)
            && !runs_tactics(node)
        {
            found.push((node, selected));
        }
        pending.extend(args(node).iter());
    }
    found
}

/// Whether one of `node`'s own children is the atom `atom`.
fn contains_atom_shallow(node: &Syntax, atom: &str) -> bool {
    args(node)
        .iter()
        .any(|child| matches!(child, Syntax::Atom { val, .. } if val == atom))
}

/// The pattern variables a `matchAlt`'s patterns bind, with their positions, or `None`
/// when a pattern has a form this module does not read. An identifier is a variable unless
/// it is qualified, heads an application, or is spelled like some constructor: the pin
/// resolves it against the open namespaces, so any constructor spelling may be one.
/// The environment's constructor spellings (the last component of each name), for telling a
/// pattern variable from a constructor, and its indexed families' constructors.
pub(crate) struct Constructors {
    pub(crate) names: HashSet<String>,
    /// The spellings of the constructors this source declares, not imported: an unqualified or
    /// dotted head spelled like one names it (`open BV` then `cons`), not an `Init` constructor
    /// spelled alike (`List.Sublist.cons`).
    pub(crate) local: HashSet<String>,
    pub(crate) indexed: Vec<IndexedConstructor>,
}

/// A constructor of a family with indices, and which of its explicit fields this module leaves
/// unread in a pattern.
///
/// The pin's use of such a field depends on how its match elaborator treats the family's
/// indices. Measured against the pinned v4.32.0 over `IVec A m` (`{n} (head : A)
/// (tail : IVec A n) : IVec A (n + 1)`), with `m` a variable the match must generalize:
/// `| .cons x t => 1` warns about `x` only. With an explicit index field (`cons (n : Nat) …`),
/// `| .cons k x t => 1` warns about `x` only as well. Over `IVec A (m + 1)` or `IVec A 2`, or
/// with the index bound by a `_` pattern, it warns about `x` and `t`. A field that is an
/// index (`k`) or whose type is an indexed family (`t`) is therefore not read. Every other
/// field (`x`, and `b : Fin (n + 1)` too) was warned about in every shape measured.
pub(crate) struct IndexedConstructor {
    pub(crate) name: Name,
    /// Whether this source declares it.
    pub(crate) local: bool,
    /// One entry per explicit field, in order: `true` when the field is not read.
    pub(crate) unread: Vec<bool>,
}

/// Which explicit fields of `ctor` (with `num_params` parameters, of a family with
/// `num_indices` indices) a pattern leaves unread: those occurring in the result type's
/// indices, and those whose type is headed by a family `indexed` names.
pub(crate) fn unread_fields(
    type_: &Expr,
    num_params: u32,
    num_indices: u32,
    indexed: impl Fn(&Name) -> bool,
) -> Vec<bool> {
    fn head(mut expr: &Expr) -> &Expr {
        while let ExprNode::App { f, .. } = expr.node() {
            expr = f;
        }
        expr
    }
    let mut binders = Vec::new();
    let mut result = type_;
    while let ExprNode::ForallE {
        binder_type,
        body,
        binder_info,
        ..
    } = result.node()
    {
        binders.push((*binder_info, binder_type));
        result = body;
    }
    let mut args = Vec::new();
    let mut applied = result;
    while let ExprNode::App { f, a } = applied.node() {
        args.push(a);
        applied = f;
    }
    // `args` runs from the last argument to the first: the indices come first.
    let indices = &args[..(num_indices as usize).min(args.len())];
    let total = binders.len();
    binders
        .iter()
        .enumerate()
        .skip(num_params as usize)
        .filter(|(_, (info, _))| *info == fln_core::expr::BinderInfo::Default)
        .map(|(position, (_, field_type))| {
            let bvar = u32::try_from(total - 1 - position).unwrap_or(u32::MAX);
            let index = indices.iter().any(|index| index.has_loose_bvar(bvar));
            let family = matches!(head(field_type).node(),
                ExprNode::Const { name, .. } if indexed(name));
            index || family
        })
        .collect()
}

fn components(name: &Name) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = name.clone();
    while !current.is_anonymous() {
        parts.push(match current.leaf_view() {
            LeafView::Str(text) => text.to_owned(),
            _ => String::new(),
        });
        current = current.parent();
    }
    parts.reverse();
    parts
}

impl Constructors {
    /// The unread fields of the indexed constructors a pattern head written `head` may name,
    /// merged, or `None` when it names none. A qualified head names the constructors whose
    /// names end with it, an unqualified or dotted one every constructor spelled like it, so
    /// the merge only ever leaves more unread.
    fn unread(&self, head: &Name) -> Option<Vec<bool>> {
        let written = components(head);
        let local = matches!(written.as_slice(), [spelling] if self.local.contains(spelling));
        let mut merged: Option<Vec<bool>> = None;
        for constructor in &self.indexed {
            if !components(&constructor.name).ends_with(&written) || (local && !constructor.local) {
                continue;
            }
            let merged = merged.get_or_insert_with(Vec::new);
            for (index, &unread) in constructor.unread.iter().enumerate() {
                match merged.get_mut(index) {
                    Some(slot) => *slot |= unread,
                    None => merged.push(unread),
                }
            }
        }
        merged
    }
}

fn pattern_variables(patterns: &Syntax, constructors: &Constructors) -> Option<Vec<(Name, usize)>> {
    let mut variables = Vec::new();
    // Each pattern, and whether it lies under a named pattern `x@p`, where the pin warns about
    // every unused field of an indexed constructor too (measured 2026-10-22).
    let mut pending = vec![(patterns, false)];
    while let Some((pattern, plain)) = pending.pop() {
        match pattern {
            Syntax::Ident { val, .. } => {
                if let LeafView::Str(text) = val.leaf_view()
                    && val.parent().is_anonymous()
                    && !constructors.names.contains(text)
                {
                    variables.push((val.clone(), original_pos(pattern)?));
                }
            }
            Syntax::Atom { .. } | Syntax::Missing => {}
            Syntax::Node { kind, args, .. } => {
                let kind = kind.to_display_string();
                match kind.as_str() {
                    "null"
                    | "Lean.Parser.Term.paren"
                    | "Lean.Parser.Term.anonymousCtor"
                    | "Lean.Parser.Term.tuple"
                    | "term_+_"
                    | "term_::_"
                    | "term[_]" => {
                        pending.extend(args.iter().map(|arg| (arg, plain)));
                    }
                    // The head is a constructor or a `match_pattern` function, never bound.
                    "Lean.Parser.Term.app" => {
                        let head = match args.first() {
                            Some(Syntax::Ident { val, .. }) => Some(val.clone()),
                            Some(head) if is_kind(head, &["Term", "dotIdent"]) => {
                                match self::args(head).get(1) {
                                    Some(Syntax::Ident { val, .. }) => Some(val.clone()),
                                    _ => None,
                                }
                            }
                            // `@C …` writes the implicit fields too, which `unread` does not
                            // count: an indexed constructor's is not read at all.
                            Some(head) if is_kind(head, &["Term", "explicit"]) => {
                                if !plain
                                    && let Some(Syntax::Ident { val, .. }) = self::args(head).get(1)
                                    && constructors.unread(val).is_some()
                                {
                                    return None;
                                }
                                None
                            }
                            _ => None,
                        };
                        let unread = head
                            .filter(|_| !plain)
                            .and_then(|head| constructors.unread(&head));
                        let Some(unread) = unread else {
                            pending.extend(args.get(1).map(|arg| (arg, plain)));
                            continue;
                        };
                        let fields = args.get(1).map(self::args).unwrap_or(&[]);
                        for (index, field) in fields.iter().enumerate() {
                            // A field past the constructor's explicit ones is not read either.
                            if !unread.get(index).copied().unwrap_or(true) {
                                pending.push((field, plain));
                            }
                        }
                    }
                    "Lean.Parser.Term.namedPattern" => {
                        pending.extend(args.first().map(|arg| (arg, plain)));
                        pending.extend(args.get(3).map(|arg| (arg, true)));
                    }
                    // The ascribed type is a term the pattern's variables may appear in.
                    "Lean.Parser.Term.typeAscription" => {
                        pending.extend(args.get(1).map(|arg| (arg, plain)));
                    }
                    "Lean.Parser.Term.hole"
                    | "Lean.Parser.Term.ellipsis"
                    | "Lean.Parser.Term.dotIdent"
                    | "Lean.Parser.Term.hygienicLParen"
                    | "num"
                    | "str"
                    | "char"
                    | "scientific" => {}
                    _ => return None,
                }
            }
        }
    }
    Some(variables)
}

/// The unused pattern variables of `command`'s `match` alternatives and equations, in source
/// order. The pin reads a pattern variable's uses only from elaborated references: the body
/// it records abstracts every alternative's variables, so a reference in the alternative is
/// the whole evidence, and an identifier with its name anywhere else in the alternative
/// over-approximates it.
pub(crate) fn unused_pattern_variables(
    command: &Syntax,
    options: &KVMap,
    constructors: &Constructors,
) -> Vec<UnusedBinder> {
    if !linted(options, Some("patternVars")) {
        return Vec::new();
    }
    let alternatives = term_scopes(command, |node| {
        is_kind(node, &["Term", "matchAlt"]).then_some(())
    });
    let mut unused = Vec::new();
    for (alternative, ()) in alternatives {
        let Some(patterns) = args(alternative).get(1) else {
            continue;
        };
        let Some(variables) = pattern_variables(patterns, constructors) else {
            continue;
        };
        for (name, at) in variables {
            if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
                continue;
            }
            if !referenced(alternative, &name, at) {
                unused.push(UnusedBinder { at, name });
            }
        }
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}

/// The binders a `fun`'s binder list names, or `None` when one has a form not read here.
/// An instance binder is left unread: the pin may count resolution as its use.
fn fun_binders(binders: &[Syntax], constructors: &Constructors) -> Option<Vec<(Name, usize)>> {
    // A binder name, a hole, or `x y` written as an application of names.
    fn idents(syntax: &Syntax) -> Option<Vec<(Name, usize)>> {
        let parts: Vec<&Syntax> = if is_kind(syntax, &["Term", "app"]) {
            std::iter::once(args(syntax).first()?)
                .chain(args(args(syntax).get(1)?))
                .collect()
        } else {
            vec![syntax]
        };
        let mut names = Vec::new();
        for part in parts {
            match part {
                Syntax::Ident { val, .. } => names.push((val.clone(), original_pos(part)?)),
                _ if is_kind(part, &["Term", "hole"]) => {}
                _ => return None,
            }
        }
        Some(names)
    }
    let mut names = Vec::new();
    for binder in binders {
        if matches!(binder, Syntax::Ident { .. }) || is_kind(binder, &["Term", "hole"]) {
            names.extend(idents(binder)?);
        } else if is_kind(binder, &["Term", "tuple"]) || is_kind(binder, &["Term", "anonymousCtor"])
        {
            // `fun (x, y) => …` matches on its argument: its names are pattern variables.
            names.extend(pattern_variables(binder, constructors)?);
        } else if is_kind(binder, &["Term", "typeAscription"])
            || is_kind(binder, &["Term", "paren"])
        {
            names.extend(idents(args(binder).get(1)?)?);
        } else if is_kind(binder, &["Term", "implicitBinder"])
            || is_kind(binder, &["Term", "strictImplicitBinder"])
        {
            for name in args(args(binder).get(1)?) {
                names.extend(idents(name)?);
            }
        } else if !is_kind(binder, &["Term", "instBinder"]) {
            return None;
        }
    }
    Some(names)
}

/// The unused binders of `command`'s `fun` terms, in source order. Inside a declaration
/// body the pin counts only elaborated references to them (the recorded body abstracts
/// them), and an identifier with the name anywhere in the `fun` over-approximates those.
pub(crate) fn unused_fun_binders(
    command: &Syntax,
    options: &KVMap,
    constructors: &Constructors,
) -> Vec<UnusedBinder> {
    // The pin's ignore functions for function arguments (`basicFun`) when `funArgs` is off.
    if !linted(options, Some("funArgs")) {
        return Vec::new();
    }
    let functions = term_scopes(command, |node| {
        is_kind(node, &["Term", "basicFun"]).then_some(())
    });
    let mut unused = Vec::new();
    for (function, ()) in functions {
        let Some(binders) = args(function).first() else {
            continue;
        };
        let Some(names) = fun_binders(args(binders), constructors) else {
            continue;
        };
        for (name, at) in names {
            if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
                continue;
            }
            if !referenced(function, &name, at) {
                unused.push(UnusedBinder { at, name });
            }
        }
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}

/// The names a binder group declares, or `None` for a form not read here. An instance
/// binder declares nothing read here: the pin may count resolution as its use.
fn group_names(binder: &Syntax) -> Option<Vec<(Name, usize)>> {
    let mut names = Vec::new();
    let mut push = |syntax: &Syntax| -> Option<()> {
        match syntax {
            Syntax::Ident { val, .. } => names.push((val.clone(), original_pos(syntax)?)),
            _ if is_kind(syntax, &["Term", "hole"]) => {}
            _ => return None,
        }
        Some(())
    };
    if matches!(binder, Syntax::Ident { .. }) || is_kind(binder, &["Term", "hole"]) {
        push(binder)?;
    } else if ["explicitBinder", "implicitBinder", "strictImplicitBinder"]
        .iter()
        .any(|kind| is_kind(binder, &["Term", kind]))
    {
        for name in args(args(binder).get(1)?) {
            push(name)?;
        }
    } else if !is_kind(binder, &["Term", "instBinder"]) {
        return None;
    }
    Some(names)
}

/// The unused binders of `command` that sit under no `fun` or pattern in the source, in source
/// order: those of `∀`s, dependent arrows, subtypes, structure-instance fields, `∃`, `Σ`, `Σ'`,
/// `×` and `×'`, an `if h :`, a `let` or `have`, and a `do` block's `let`, `←`, `have` and
/// `for`. Such a binder is in scope only in the terms it binds, so the pin's whole evidence is
/// a reference there. The pin ignores an explicit dependent arrow's binder (`(x : A) → B`), not
/// an implicit one (`{x : A} → B`). A subtype's binder (`{x : T // p}`) and a field's
/// (`f x := v`) sit under no `fun` in the source, so `funArgs` does not ignore them. A `let mut`
/// is not read: a reassignment rebinds its name.
pub(crate) fn unused_type_binders(command: &Syntax, options: &KVMap) -> Vec<UnusedBinder> {
    if !linted(options, None) {
        return Vec::new();
    }
    let groups = |binders: &Syntax| {
        args(binders)
            .iter()
            .map(group_names)
            .collect::<Option<Vec<_>>>()
            .map(|groups| groups.concat())
    };
    let scopes = term_scopes(command, |node| -> Option<Vec<Binding<'_>>> {
        let whole = |names: Vec<(Name, usize)>| vec![(names, vec![node])];
        if is_kind(node, &["Term", "forall"]) {
            args(node).get(1).and_then(groups).map(whole)
        } else if is_kind(node, &["Term", "depArrow"]) {
            args(node)
                .first()
                .filter(|binder| !is_kind(binder, &["Term", "explicitBinder"]))
                .and_then(group_names)
                .map(whole)
        } else if node.kind() == Some(&Name::from_components(["term{_:_//_}"])) {
            args(node).get(1).and_then(group_names).map(whole)
        } else if is_kind(node, &["Term", "structInstField"]) {
            args(node)
                .get(1)
                .and_then(|field| args(field).first())
                .and_then(groups)
                .map(whole)
        } else if node.kind() == Some(&Name::from_components(["termDepIfThenElse"])) {
            // `if h : c then t else e`: `h` is bound in `t` and `e`.
            let names = binder_idents(args(node).get(1)?);
            Some(vec![(names, args(node).iter().skip(5).collect())])
        } else if let Some(binders) = binder_notation(node) {
            Some(whole(binder_idents(binders)))
        } else if ["let", "have"]
            .iter()
            .any(|kind| is_kind(node, &["Term", kind]))
        {
            // `let x := v; b`: `x` is bound in `b`.
            let name = let_name(args(node).get(2)?)?;
            Some(vec![(vec![name], args(node).get(4).into_iter().collect())])
        } else if is_kind(node, &["Term", "doSeqIndent"])
            || is_kind(node, &["Term", "doSeqBracketed"])
        {
            // A `do` block's binding is in scope in the items after it.
            let items =
                args(args(node).get(usize::from(is_kind(node, &["Term", "doSeqBracketed"])))?);
            let mut bindings = Vec::new();
            for (index, item) in items.iter().enumerate() {
                if let Some(name) = args(item).first().and_then(do_binding) {
                    bindings.push((vec![name], items[index + 1..].iter().collect()));
                }
            }
            Some(bindings)
        } else if is_kind(node, &["Term", "doFor"]) {
            // `for x in xs do body`: `x` is bound in `body`.
            let declaration = args(args(node).get(1)?).first()?;
            if !is_kind(declaration, &["Term", "doForDecl"]) {
                return None;
            }
            let name = args(declaration).get(1).and_then(ident)?;
            Some(vec![(vec![name], args(node).get(3).into_iter().collect())])
        } else {
            None
        }
    });
    let mut unused = Vec::new();
    for (_, bindings) in scopes {
        for (names, bodies) in bindings {
            for (name, at) in names {
                if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
                    continue;
                }
                if !bodies.iter().any(|body| referenced(body, &name, at)) {
                    unused.push(UnusedBinder { at, name });
                }
            }
        }
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}

/// Names bound together, and the terms that are their scope.
type Binding<'a> = (Vec<(Name, usize)>, Vec<&'a Syntax>);

/// An identifier with its name and position.
fn ident(syntax: &Syntax) -> Option<(Name, usize)> {
    match syntax {
        Syntax::Ident { val, .. } => Some((val.clone(), original_pos(syntax)?)),
        _ => None,
    }
}

/// The names `binderIdent`s anywhere in `syntax` declare (a hole declares none).
fn binder_idents(syntax: &Syntax) -> Vec<(Name, usize)> {
    let mut names = Vec::new();
    walk(syntax, |node| {
        if node.kind() == Some(&Name::from_components(["Lean", "binderIdent"]))
            && let Some(name) = args(node).first().and_then(ident)
        {
            names.push(name);
        }
        false
    });
    names
}

/// The binders of an `∃`, `Σ` or `Σ'` (`∃ x y : A, p`) or of a `×`/`×'` group (`(x : A) × B`),
/// whose scope is the whole notation.
fn binder_notation(node: &Syntax) -> Option<&Syntax> {
    let kind = node.kind()?;
    if ["term∃_,_", "termΣ_,_", "termΣ'_,_"]
        .iter()
        .any(|notation| *kind == Name::str(Name::anonymous(), *notation))
    {
        args(node).get(1)
    } else if ["term_×__1", "term_×'__1"]
        .iter()
        .any(|notation| *kind == Name::str(Name::anonymous(), *notation))
    {
        args(node).first()
    } else {
        None
    }
}

/// The name a `letDecl` binds with `letIdDecl` and no function arguments.
fn let_name(declaration: &Syntax) -> Option<(Name, usize)> {
    if !is_kind(declaration, &["Term", "letDecl"]) {
        return None;
    }
    let local = args(declaration).first()?;
    if !is_kind(local, &["Term", "letIdDecl"]) || !args(args(local).get(1)?).is_empty() {
        return None;
    }
    let id = args(local).first()?;
    if !is_kind(id, &["Term", "letId"]) {
        return None;
    }
    args(id).first().and_then(ident)
}

/// The name a `do` element binds: `let x := v`, `let x ← e` and `have x := v`, not `let mut`.
fn do_binding(element: &Syntax) -> Option<(Name, usize)> {
    if is_kind(element, &["Term", "doLet"]) || is_kind(element, &["Term", "doLetArrow"]) {
        if !args(args(element).get(1)?).is_empty() {
            return None;
        }
        let declaration = args(element).get(3)?;
        if is_kind(declaration, &["Term", "doIdDecl"]) {
            return args(declaration).first().and_then(ident);
        }
        return let_name(declaration);
    }
    if is_kind(element, &["Term", "doHave"]) {
        return let_name(args(element).get(2)?);
    }
    None
}

/// The binders a `∀`/`fun` telescope introduces, by name, outermost first.
fn telescope(mut expr: &Expr, lambda: bool) -> Vec<(&Name, &Expr)> {
    let mut binders = Vec::new();
    loop {
        match expr.node() {
            ExprNode::ForallE {
                binder_name, body, ..
            } if !lambda => {
                binders.push((binder_name, body));
                expr = body;
            }
            ExprNode::Lam {
                binder_name, body, ..
            } if lambda => {
                binders.push((binder_name, body));
                expr = body;
            }
            ExprNode::MData { expr: inner, .. } => expr = inner,
            _ => return binders,
        }
    }
}

/// The unused signature binders of `command`, a parsed `def`, `theorem`, `abbrev`,
/// `instance` or `example`, given its admitted `type_` and `value`, in source order.
pub(crate) fn unused_signature_binders(
    command: &Syntax,
    type_: &Expr,
    value: &Expr,
    options: &KVMap,
) -> Vec<UnusedBinder> {
    let Some((modifiers, declaration, body)) = decided(command) else {
        return Vec::new();
    };
    // The pin's ignore function for foreign definitions (`@[extern]`, `implemented_by`).
    if !linted(options, Some("funArgs")) || contains_atom(modifiers, &["extern", "implemented_by"])
    {
        return Vec::new();
    }
    let Some(signature) = args(declaration).iter().find(|part| {
        is_kind(part, &["Command", "optDeclSig"]) || is_kind(part, &["Command", "declSig"])
    }) else {
        return Vec::new();
    };
    let Some(slots) = args(signature)
        .first()
        .and_then(|binders| signature_slots(args(binders)))
    else {
        return Vec::new();
    };
    if slots.is_empty() {
        return Vec::new();
    }
    // Align the slots with the admitted telescope: section variables and automatically
    // bound implicits come first, so the signature starts at the earliest matching index.
    let pis = telescope(type_, false);
    let lambdas = telescope(value, true);
    let matches = |names: &[(&Name, &Expr)], start: usize| {
        slots.iter().enumerate().all(|(offset, slot)| {
            names
                .get(start + offset)
                .is_some_and(|(name, _)| slot.as_ref().is_none_or(|(slot, _)| *name == slot))
        })
    };
    let Some(start) =
        (0..pis.len()).find(|&start| matches(&pis, start) && matches(&lambdas, start))
    else {
        return Vec::new();
    };
    let mut unused = Vec::new();
    for (offset, slot) in slots.iter().enumerate() {
        let Some((name, at)) = slot else { continue };
        // `_x` is the suggested way to keep an intentionally unused binder.
        if matches!(name.leaf_view(), LeafView::Str(text) if text.starts_with('_')) {
            continue;
        }
        let index = start + offset;
        let syntax = match body {
            Body::Terms => declaration,
            Body::Tactics => signature,
        };
        if referenced(syntax, name, *at)
            || pis[index].1.has_loose_bvar(0)
            || lambdas[index].1.has_loose_bvar(0)
        {
            continue;
        }
        unused.push(UnusedBinder {
            at: *at,
            name: name.clone(),
        });
    }
    unused.sort_by_key(|binder| binder.at);
    unused
}
