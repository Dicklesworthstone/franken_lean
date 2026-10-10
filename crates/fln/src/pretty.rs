//! A bounded delaborator: kernel terms printed as the pin's `lean` prints them for
//! `#check` (`Lean.PrettyPrinter.Delaborator` with default options).
//!
//! Covered: constants and universe levels (`Type u_1`, `Sort (max u v)`), applications
//! with implicit and instance arguments hidden (`pp.explicit false`), the arithmetic,
//! relation and connective notations of `Init` (with their precedences and
//! associativity), numerals (`OfNat.ofNat _ n _`), non-dependent arrows, dependent
//! binders grouped as the pin groups them (`{α β : Type}`, `(n m : Nat)`, `[Inhabited α]`),
//! `∀` for propositions, `fun`, `×`, and the signature form of `#check ident`
//! (`Nat.succ (n : Nat) : Nat`, `delabConstWithSignature`).
//!
//! Lines break where the pin's do: each construct builds the [`format::Format`] the pin's
//! formatter builds from its syntax (every term node `fill (nest 2 …)`, a line at each
//! spaced token), rendered by a port of `Std.Format.pretty` at width 120.
//!
//! Anything else is reported as unsupported rather than printed differently: a caller
//! must not show text the pin would not show.
use super::*;
use fln_core::expr::NatLit;
use fln_core::level::LevelView;

pub mod format;
use format::Format;

/// Why a term could not be printed the pin's way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported(pub &'static str);

type Printed = Result<String, Unsupported>;

/// Precedences of the pin's notations (`Init/Notation.lean`, `Init/Core.lean`).
const MAX_PREC: u32 = 1024;
const ARROW_PREC: u32 = 25;

struct Infix {
    function: &'static str,
    /// Total arguments of the fully applied function; the last two are the operands.
    arity: usize,
    symbol: &'static str,
    precedence: u32,
    right: bool,
}

const INFIXES: &[Infix] = &[
    Infix {
        function: "HAdd.hAdd",
        arity: 6,
        symbol: "+",
        precedence: 65,
        right: false,
    },
    Infix {
        function: "HSub.hSub",
        arity: 6,
        symbol: "-",
        precedence: 65,
        right: false,
    },
    Infix {
        function: "HMul.hMul",
        arity: 6,
        symbol: "*",
        precedence: 70,
        right: false,
    },
    Infix {
        function: "HDiv.hDiv",
        arity: 6,
        symbol: "/",
        precedence: 70,
        right: false,
    },
    Infix {
        function: "HMod.hMod",
        arity: 6,
        symbol: "%",
        precedence: 70,
        right: false,
    },
    Infix {
        function: "HPow.hPow",
        arity: 6,
        symbol: "^",
        precedence: 75,
        right: true,
    },
    Infix {
        function: "HAppend.hAppend",
        arity: 6,
        symbol: "++",
        precedence: 65,
        right: false,
    },
    Infix {
        function: "Eq",
        arity: 3,
        symbol: "=",
        precedence: 50,
        right: false,
    },
    Infix {
        function: "Ne",
        arity: 3,
        symbol: "≠",
        precedence: 50,
        right: false,
    },
    Infix {
        function: "BEq.beq",
        arity: 4,
        symbol: "==",
        precedence: 50,
        right: false,
    },
    Infix {
        function: "LT.lt",
        arity: 4,
        symbol: "<",
        precedence: 50,
        right: false,
    },
    Infix {
        function: "LE.le",
        arity: 4,
        symbol: "≤",
        precedence: 50,
        right: false,
    },
    Infix {
        function: "GT.gt",
        arity: 4,
        symbol: ">",
        precedence: 50,
        right: false,
    },
    Infix {
        function: "GE.ge",
        arity: 4,
        symbol: "≥",
        precedence: 50,
        right: false,
    },
    Infix {
        function: "And",
        arity: 2,
        symbol: "∧",
        precedence: 35,
        right: true,
    },
    Infix {
        function: "Or",
        arity: 2,
        symbol: "∨",
        precedence: 30,
        right: true,
    },
    Infix {
        function: "Iff",
        arity: 2,
        symbol: "↔",
        precedence: 20,
        right: false,
    },
    Infix {
        function: "Prod",
        arity: 2,
        symbol: "×",
        precedence: 35,
        right: true,
    },
    Infix {
        function: "List.cons",
        arity: 3,
        symbol: "::",
        precedence: 67,
        right: true,
    },
];

/// An application's head and arguments.
fn spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut head = e.clone();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        let next = f.clone();
        head = next;
    }
    args.reverse();
    (head, args)
}

/// A term laid out as the pin's formatter lays it out.
type Doc = Result<Format, Unsupported>;

/// The pin's message width (`format.width`, `Std.Format.defWidth`).
const WIDTH: usize = 120;

/// A term node as the pin's formatter groups it: `fill (nest 2 …)`
/// (`categoryParser.formatter`, vendored `PrettyPrinter/Formatter.lean`).
fn node(content: Format) -> Format {
    content.nest(2).fill()
}

/// `(…)` around a grouped term when its precedence is below the context's: the `paren`
/// node, whose `ppDedentIfGrouped` dedents the inner term (vendored `Parser/Term.lean`).
fn paren_doc(doc: Format, inner: u32, outer: u32) -> Format {
    if inner < outer {
        node(Format::text("(").then(doc.nest(-2)).then(Format::text(")")))
    } else {
        doc
    }
}

/// The digits `Nat.toSuperscriptString` writes, `⁰` to `⁹`.
const SUPERSCRIPTS: &str = "⁰¹²³⁴⁵⁶⁷⁸⁹";

/// A layout on one line, for comparing two terms' text.
fn flat(doc: &Format) -> String {
    doc.pretty(usize::MAX / 4)
}

fn nat_decimal(value: &NatLit) -> String {
    if let Some(small) = value.to_u64() {
        return small.to_string();
    }
    // Long division of little-endian base-2^64 limbs by 10^19.
    let mut limbs: Vec<u64> = value.limbs_le().to_vec();
    let mut chunks = Vec::new();
    const BASE: u64 = 10_000_000_000_000_000_000;
    while limbs.iter().any(|limb| *limb != 0) {
        let mut remainder: u128 = 0;
        for limb in limbs.iter_mut().rev() {
            let current = (remainder << 64) | u128::from(*limb);
            *limb = u64::try_from(current / u128::from(BASE)).unwrap_or(u64::MAX);
            remainder = current % u128::from(BASE);
        }
        chunks.push(u64::try_from(remainder).unwrap_or(0));
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
    }
    let mut out = chunks
        .pop()
        .map_or_else(|| "0".to_owned(), |c| c.to_string());
    for chunk in chunks.into_iter().rev() {
        out.push_str(&format!("{chunk:019}"));
    }
    out
}

fn string_literal(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A level as the pin prints it, at application-argument precedence when `argument`.
fn level(level: &Level, argument: bool) -> Printed {
    // `u + k` and `k` are the offset forms.
    let mut base = level;
    let mut offset = 0u64;
    while let LevelView::Succ(inner) = base.view() {
        base = inner;
        offset += 1;
    }
    let text = match base.view() {
        LevelView::Zero => return Ok(offset.to_string()),
        LevelView::Param(name) => {
            if offset == 0 {
                return Ok(escaped_name(name));
            }
            format!("{} + {offset}", escaped_name(name))
        }
        LevelView::Max(a, b) | LevelView::IMax(a, b) => {
            let keyword = if matches!(base.view(), LevelView::Max(..)) {
                "max"
            } else {
                "imax"
            };
            let inner = format!(
                "{keyword} {} {}",
                self::level(a, true)?,
                self::level(b, true)?
            );
            if offset == 0 {
                inner
            } else {
                format!("({inner}) + {offset}")
            }
        }
        LevelView::MVar(_) => return Err(Unsupported("a universe metavariable")),
        LevelView::Succ(_) => unreachable!("offsets were peeled"),
    };
    Ok(if argument { format!("({text})") } else { text })
}

fn sort(level_: &Level) -> Printed {
    // The pin prints inferred sorts normalized (`Sort (imax 1 0)` is `Prop`).
    let normalized = level_.normalize();
    let level_ = &normalized;
    if level_.is_zero() {
        return Ok("Prop".to_owned());
    }
    if let LevelView::Succ(inner) = level_.view() {
        return Ok(if inner.is_zero() {
            "Type".to_owned()
        } else {
            format!("Type {}", level(inner, true)?)
        });
    }
    Ok(format!("Sort {}", level(level_, true)?))
}

/// Whether a name prints as itself (the pin shows other binder names as `x✝`).
///
/// Inaccessible: anonymous names, the elaborator's generated names (a numeric component,
/// or the `_fln…` locals standing in for the pin's macro-scoped `inst✝`/`x✝`), and
/// macro-scoped names.
fn accessible(name: &Name) -> bool {
    if name.is_anonymous() {
        return false;
    }
    let mut current = name.clone();
    while !current.is_anonymous() {
        match current.leaf_view() {
            LeafView::Str(part) => {
                if part.starts_with("_hyg") || part.starts_with("_fln") || part.contains('✝') {
                    return false;
                }
            }
            _ => return false,
        }
        current = current.parent();
    }
    true
}

/// One component as the pin's `escapePart` writes it (vendored `Init/Meta/Defs.lean`): an
/// identifier as it is, anything else between `«` and `»`, and unchanged when it holds a `»`
/// (`None` at the pin, which then prints the component as it is). `force` escapes even an
/// identifier.
fn escaped_part(part: &str, force: bool) -> String {
    let mut chars = part.chars();
    let identifier = chars.next().is_some_and(fln_syntax::token::is_id_first)
        && chars.all(fln_syntax::token::is_id_rest);
    if (identifier && !force) || part.contains('»') {
        part.to_owned()
    } else {
        format!("«{part}»")
    }
}

/// Whether `text` is a token of the implicit `Init` table, the pin's `isToken` when it
/// prints a name from a file without a header.
fn is_token(text: &str) -> bool {
    fln_parse::reference_tokens::implicit_init_table().contains(text)
}

/// A name as the pin's `Name.toStringWithToken` prints it, with `escape := true` (vendored
/// `Init/Meta/Defs.lean`, `toStringWithSep`). A component that is not an identifier is
/// written `«…»`, and so is a root component that is a token. A later component is forced
/// only when the dotted prefix would read as a token. Inaccessible names (`✝`,
/// `_inaccessible`), macro-scoped names and the delaborator's pseudo-syntax (`_`, `#…`,
/// `?…`) print as they are.
fn escaped_name(name: &Name) -> String {
    // Components root first; `Err` is a numeric component.
    let mut parts: Vec<Result<String, u64>> = Vec::new();
    let mut current = name.clone();
    loop {
        let part = match current.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Str(text) => Ok(text.to_owned()),
            LeafView::Num(value) => Err(value),
        };
        parts.push(part);
        current = current.parent();
    }
    parts.reverse();
    let pseudo = match parts.first() {
        Some(Ok(root)) => {
            (parts.len() == 1 && root == "_") || root.starts_with('#') || root.starts_with('?')
        }
        _ => false,
    };
    // `isInaccessibleUserName`: the last string component, looking through numbers.
    let inaccessible = parts.iter().rev().find_map(|part| match part {
        Ok(text) => Some(text.contains('✝') || text == "_inaccessible"),
        Err(_) => None,
    }) == Some(true);
    if pseudo || inaccessible || name.has_macro_scopes() {
        return name.to_display_string();
    }
    let mut text = String::new();
    for (index, part) in parts.iter().enumerate() {
        match part {
            Ok(component) if index == 0 => {
                text = escaped_part(component, is_token(component));
            }
            Ok(component) => {
                let plain = format!("{text}.{}", escaped_part(component, false));
                text = if is_token(&plain) {
                    format!("{text}.{}", escaped_part(component, true))
                } else {
                    plain
                };
            }
            Err(value) => {
                if index > 0 {
                    text.push('.');
                }
                text.push_str(&value.to_string());
            }
        }
    }
    text
}

fn binder_name(name: &Name) -> String {
    if accessible(name) {
        escaped_name(name)
    } else if name.is_anonymous() {
        "x✝".to_owned()
    } else {
        format!("{}✝", name.to_display_string())
    }
}

/// The printer: an environment for binder information and proposition tests, and the
/// names and types of the binders in scope (innermost last).
pub struct Printer<'a> {
    env: &'a Environment,
    scope: Option<&'a fln_elab::source::scope::SourceScope>,
    names: Vec<String>,
    /// Each binder's type, relative to the binders outside it.
    types: Vec<Expr>,
    /// Inside a call to [`Printer::expr`]: the root call decides `proofs`.
    nested: bool,
    /// The pin's `pp.proofs`: false by default, true when the printed term is itself a
    /// proof. When false, a proof inside the term that is not atomic prints as `⋯`.
    proofs: bool,
    budget: usize,
}

/// The pin's `Expr.isAtomic`: no subterms.
fn atomic(e: &Expr) -> bool {
    matches!(
        e.node(),
        ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. }
    )
}

/// Whether a type ends in `Prop` after its `∀`s.
fn ends_in_prop(type_: &Expr) -> bool {
    let mut type_ = type_;
    loop {
        match type_.node() {
            ExprNode::ForallE { body, .. } => type_ = body,
            ExprNode::MData { expr, .. } => type_ = expr,
            _ => return matches!(type_.node(), ExprNode::Sort { level } if level.is_zero()),
        }
    }
}

impl<'a> Printer<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self {
            env,
            scope: None,
            names: Vec::new(),
            types: Vec::new(),
            nested: false,
            proofs: false,
            budget: 100_000,
        }
    }

    /// Enter a binder: its shown name and its type.
    fn bind(&mut self, shown: String, type_: &Expr) {
        self.names.push(shown);
        self.types.push(type_.clone());
    }

    /// Leave every binder entered after `depth`.
    fn unbind_to(&mut self, depth: usize) {
        self.names.truncate(depth);
        self.types.truncate(depth);
    }

    /// Print current-module private names through their source spelling, as
    /// the pin's default `pp.privateNames = false` delaborator does. All core
    /// lookups and notation decisions retain the original declaration name.
    pub fn in_scope(env: &'a Environment, scope: &'a fln_elab::source::scope::SourceScope) -> Self {
        Self {
            scope: Some(scope),
            ..Self::new(env)
        }
    }

    fn display_name(&self, name: &Name) -> String {
        self.scope.map_or_else(
            || escaped_name(name),
            |scope| escaped_name(&scope.user_name(name)),
        )
    }

    fn tick(&mut self) -> Result<(), Unsupported> {
        self.budget = self
            .budget
            .checked_sub(1)
            .ok_or(Unsupported("the term is too large to print"))?;
        Ok(())
    }

    /// The binder infos of a constant's leading binders.
    fn binder_infos(&self, name: &Name) -> Vec<BinderInfo> {
        let mut infos = Vec::new();
        let Some(info) = self.env.find(name) else {
            return infos;
        };
        let mut type_ = &info.constant_val().type_;
        while let ExprNode::ForallE {
            body, binder_info, ..
        } = type_.node()
        {
            infos.push(*binder_info);
            type_ = body;
        }
        infos
    }

    /// Whether `e` is (syntactically) a proposition: a sort-`Prop` application, a
    /// connective, or a `∀` into one. The head is a constant whose type ends in `Prop`, or
    /// a bound variable whose type does (a motive into `Prop`).
    fn is_prop(&self, e: &Expr) -> bool {
        Self::prop_in(self.env, &self.types, e)
    }

    /// [`Printer::is_prop`] for `e` under the binder types `scope` (innermost last).
    fn prop_in(env: &Environment, scope: &[Expr], e: &Expr) -> bool {
        let mut local: Vec<&Expr> = Vec::new();
        let mut e = e;
        loop {
            match e.node() {
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    local.push(binder_type);
                    e = body;
                }
                ExprNode::MData { expr, .. } => e = expr,
                _ => break,
            }
        }
        let (head, _) = spine(e);
        match head.node() {
            ExprNode::Const { name, .. } => env
                .find(name)
                .is_some_and(|info| ends_in_prop(&info.constant_val().type_)),
            ExprNode::BVar { idx } => {
                let idx = usize::try_from(*idx).unwrap_or(usize::MAX);
                if idx < local.len() {
                    ends_in_prop(local[local.len() - 1 - idx])
                } else {
                    let outer = idx - local.len();
                    scope
                        .len()
                        .checked_sub(outer + 1)
                        .is_some_and(|at| ends_in_prop(&scope[at]))
                }
            }
            _ => false,
        }
    }

    /// Whether `e` is a proof: its type is a proposition. The type is read from the head's
    /// type, which suffices for a constant or a bound variable at the head.
    fn is_proof(&self, e: &Expr) -> bool {
        let (head, _) = spine(e);
        match head.node() {
            ExprNode::Const { name, .. } => self
                .env
                .find(name)
                .is_some_and(|info| Self::prop_in(self.env, &[], &info.constant_val().type_)),
            ExprNode::BVar { idx } => {
                let idx = usize::try_from(*idx).unwrap_or(usize::MAX);
                // A binder's type is relative to the binders outside it.
                self.types
                    .len()
                    .checked_sub(idx + 1)
                    .is_some_and(|at| Self::prop_in(self.env, &self.types[..at], &self.types[at]))
            }
            _ => false,
        }
    }

    /// `e` as the pin prints it in a message, broken at the pin's width.
    pub fn expr(&mut self, e: &Expr, outer: u32) -> Printed {
        self.doc(e, outer).map(|doc| doc.pretty(WIDTH))
    }

    /// `#check e`'s line for a term that is not a constant: `e : type` (`m!"{e} : {type}"`,
    /// vendored `Elab/BuiltinCommand.lean`), broken at the pin's width.
    pub fn typed(&mut self, value: &Expr, type_: &Expr) -> Printed {
        let value = self.doc(value, 0)?;
        let type_ = self.doc(type_, 0)?;
        Ok(value.then(Format::text(" : ")).then(type_).pretty(WIDTH))
    }

    /// The same with the term as written in the source.
    pub fn typed_text(&mut self, term: &str, type_: &Expr) -> Printed {
        let type_ = self.doc(type_, 0)?;
        Ok(Format::text(format!("{term} : ")).then(type_).pretty(WIDTH))
    }

    /// `e` as the pin's formatter lays it out, with the pin's `pp.proofs`: a proof inside the
    /// printed term that is not atomic is `⋯`, unless the term itself is a proof (the
    /// delaborator then sets `pp.proofs`, vendored `PrettyPrinter/Delaborator/Basic.lean:510-514`).
    pub fn doc(&mut self, e: &Expr, outer: u32) -> Doc {
        if self.nested {
            if !self.proofs && !atomic(e) && self.is_proof(e) {
                return Ok(Format::text("⋯"));
            }
            return self.subterm(e, outer);
        }
        self.nested = true;
        self.proofs = self.is_proof(e);
        let printed = self.subterm(e, outer);
        self.nested = false;
        // The root is always grouped (`formatCategory` is `fill (nest 2 …)` with no
        // `isUngrouped` check), so a `fun` that is ungrouped as a child is grouped here.
        let lambda = matches!(e.node(), ExprNode::Lam { .. }) && outer == 0;
        printed.map(|doc| if lambda { node(doc) } else { doc })
    }

    fn subterm(&mut self, e: &Expr, outer: u32) -> Doc {
        self.tick()?;
        match e.node() {
            ExprNode::BVar { idx } => {
                let idx = usize::try_from(*idx).unwrap_or(usize::MAX);
                self.names
                    .len()
                    .checked_sub(idx + 1)
                    .and_then(|at| self.names.get(at))
                    .cloned()
                    .map(Format::text)
                    .ok_or(Unsupported("a loose bound variable"))
            }
            ExprNode::FVar { .. } => Err(Unsupported("a free variable")),
            ExprNode::MVar { .. } => Err(Unsupported("a metavariable")),
            ExprNode::Sort { level } => {
                let text = sort(level)?;
                let atomic = !text.contains(' ');
                let doc = Format::text(text);
                Ok(if atomic {
                    doc
                } else {
                    paren_doc(doc, MAX_PREC - 1, outer)
                })
            }
            ExprNode::Const { name, .. } => Ok(Format::text(self.constant(name))),
            ExprNode::Lit { literal } => Ok(Format::text(match literal {
                Literal::Nat(value) => nat_decimal(value),
                Literal::Str(text) => string_literal(text),
            })),
            ExprNode::MData { expr, .. } => self.doc(expr, outer),
            ExprNode::App { .. } => self.application(e, outer),
            ExprNode::ForallE { .. } => self.pi(e, outer),
            ExprNode::Lam { .. } => {
                // `fun` is ungrouped (`ppAllowUngrouped`): `fun` ++ ppGroup(binders ++ " =>")
                // ++ line ++ body (vendored `Parser/Term.lean`, `basicFun`).
                let mut binders = Format::Nil;
                let mut body = e;
                let depth = self.names.len();
                while let ExprNode::Lam {
                    binder_name: name,
                    binder_type,
                    body: inner,
                    ..
                } = body.node()
                {
                    let shown = self.bound_name(name, inner);
                    binders = binders.then(Format::Line).then(Format::text(shown.clone()));
                    self.bind(shown, binder_type);
                    body = inner;
                }
                let printed = self.doc(body, 0);
                self.unbind_to(depth);
                let fun = Format::text("fun")
                    .then(node(binders.then(Format::text(" =>"))))
                    .then(Format::Line)
                    .then(printed?);
                Ok(if outer > 0 {
                    node(Format::text("(").then(fun).then(Format::text(")")))
                } else {
                    fun
                })
            }
            // `let x : T := v; x` is how a type ascription `(v : T)` elaborates here; the
            // pin's term is `v` itself.
            ExprNode::LetE { value, body, .. }
                if matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
            {
                self.doc(value, outer)
            }
            // At the top of the printed term the pin breaks a `let` after its `;` with no
            // indentation; nested inside another construct it indents by the enclosing
            // group's width, which is not reproduced.
            ExprNode::LetE {
                decl_name: name,
                type_,
                value,
                body,
                ..
            } if outer == 0 && self.names.is_empty() => {
                let value = self.doc(value, 0)?;
                let shown = binder_name(name);
                let depth = self.names.len();
                self.bind(shown.clone(), type_);
                let printed = self.doc(body, 0);
                self.unbind_to(depth);
                Ok(Format::text(format!("let {shown} := "))
                    .then(value)
                    .then(Format::text(";\n"))
                    .then(printed?))
            }
            ExprNode::LetE { .. } => Err(Unsupported("a nested let expression")),
            ExprNode::Proj { idx, expr, .. } => Ok(node(
                self.doc(expr, MAX_PREC)?
                    .then(Format::text(format!(".{}", idx + 1))),
            )),
        }
    }

    fn application(&mut self, e: &Expr, outer: u32) -> Doc {
        let (head, args) = spine(e);
        if let ExprNode::Const { name, .. } = head.node() {
            let text = name.to_display_string();
            if text == "OfNat.ofNat"
                && args.len() == 3
                && let ExprNode::Lit {
                    literal: Literal::Nat(value),
                } = args[1].node()
            {
                return Ok(Format::text(nat_decimal(value)));
            }
            // `notation:max "¬" p:40 => Not p`.
            if text == "Not" && args.len() == 1 {
                return Ok(paren_doc(
                    node(Format::text("¬").then(self.doc(&args[0], 40)?)),
                    MAX_PREC,
                    outer,
                ));
            }
            // `[a, b, …]` (the `List.cons`/`List.nil` unexpanders); an open tail is `::`.
            if text == "List.cons" && args.len() == 3 {
                let mut elements = vec![args[1].clone()];
                let mut tail = args[2].clone();
                loop {
                    self.tick()?;
                    let (tail_head, tail_args) = spine(&tail);
                    let ExprNode::Const { name, .. } = tail_head.node() else {
                        break;
                    };
                    let name = name.to_display_string();
                    if name == "List.cons" && tail_args.len() == 3 {
                        elements.push(tail_args[1].clone());
                        tail = tail_args[2].clone();
                        continue;
                    }
                    if name == "List.nil" && tail_args.len() == 1 {
                        // `"[" sepBy term ", " "]"`: a line after each comma.
                        let mut shown = Format::Nil;
                        for (index, element) in elements.iter().enumerate() {
                            if index > 0 {
                                shown = shown.then(Format::text(",")).then(Format::Line);
                            }
                            shown = shown.then(self.doc(element, 0)?);
                        }
                        return Ok(node(Format::text("[").then(shown).then(Format::text("]"))));
                    }
                    break;
                }
            }
            if text == "List.nil" && args.len() == 1 {
                return Ok(Format::text("[]"));
            }
            if let Some(infix) = INFIXES
                .iter()
                .find(|infix| infix.function == text && infix.arity == args.len())
            {
                let (lhs_prec, rhs_prec) = if infix.right {
                    (infix.precedence + 1, infix.precedence)
                } else if matches!(infix.symbol, "=" | "≠" | "==" | "<" | "≤" | ">" | "≥" | "↔")
                {
                    (infix.precedence + 1, infix.precedence + 1)
                } else {
                    (infix.precedence, infix.precedence + 1)
                };
                // `infixl:65 " + "`: the token's trailing space is a line.
                let lhs = self.doc(&args[args.len() - 2], lhs_prec)?;
                let rhs = self.doc(&args[args.len() - 1], rhs_prec)?;
                return Ok(paren_doc(
                    node(
                        lhs.then(Format::text(format!(" {}", infix.symbol)))
                            .then(Format::Line)
                            .then(rhs),
                    ),
                    infix.precedence,
                    outer,
                ));
            }
            let infos = self.binder_infos(name);
            // Generalized field notation: `C.f r …` is `r.f …` when `r` is `C.f`'s first
            // explicit argument and has type `C …` (never on a numeric literal).
            if let Some((receiver, field)) = self.field_receiver(name, &infos, &args) {
                let projection = node(
                    self.doc(&args[receiver], MAX_PREC)?
                        .then(Format::text(format!(".{field}"))),
                );
                let mut shown = projection;
                let mut applied = false;
                for (index, arg) in args.iter().enumerate() {
                    let explicit = infos
                        .get(index)
                        .is_none_or(|info| *info == BinderInfo::Default);
                    if explicit && index != receiver {
                        shown = shown.then(Format::Line).then(self.doc(arg, MAX_PREC)?);
                        applied = true;
                    }
                }
                return Ok(if applied {
                    paren_doc(node(shown), MAX_PREC - 1, outer)
                } else {
                    shown
                });
            }
            let mut shown = Format::Nil;
            let mut applied = false;
            for (index, arg) in args.iter().enumerate() {
                let explicit = infos
                    .get(index)
                    .is_none_or(|info| *info == BinderInfo::Default);
                if explicit {
                    shown = shown.then(Format::Line).then(self.doc(arg, MAX_PREC)?);
                    applied = true;
                }
            }
            let text = self.display_name(name);
            if !applied {
                return Ok(Format::text(text));
            }
            // `app := many1 argument`, each argument after a line (`checkWsBefore`).
            return Ok(paren_doc(
                node(Format::text(text).then(shown)),
                MAX_PREC - 1,
                outer,
            ));
        }
        let mut shown = self.doc(&head, MAX_PREC)?;
        for arg in &args {
            shown = shown.then(Format::Line).then(self.doc(arg, MAX_PREC)?);
        }
        Ok(paren_doc(node(shown), MAX_PREC - 1, outer))
    }

    /// The receiver index and field name when `C.f args` prints as `receiver.f`.
    fn field_receiver(
        &self,
        name: &Name,
        infos: &[BinderInfo],
        args: &[Expr],
    ) -> Option<(usize, String)> {
        let LeafView::Str(field) = name.leaf_view() else {
            return None;
        };
        let namespace = name.parent();
        if namespace.is_anonymous() {
            return None;
        }
        let receiver = infos.iter().position(|info| *info == BinderInfo::Default)?;
        let arg = args.get(receiver)?;
        let literal = matches!(arg.node(), ExprNode::Lit { .. })
            || matches!(spine(arg).0.node(),
                ExprNode::Const { name, .. } if name.to_display_string() == "OfNat.ofNat");
        if literal {
            return None;
        }
        // The receiver binder's type, from the constant's signature.
        let mut type_ = &self.env.find(name)?.constant_val().type_;
        for _ in 0..receiver {
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return None;
            };
            type_ = body;
        }
        let ExprNode::ForallE { binder_type, .. } = type_.node() else {
            return None;
        };
        match spine(binder_type).0.node() {
            ExprNode::Const { name: head, .. } if *head == namespace => {
                Some((receiver, escaped_part(field, false)))
            }
            _ => None,
        }
    }

    /// A bare constant: `@c` when it has implicit binders the pin would otherwise fill.
    pub fn constant(&self, name: &Name) -> String {
        let explicit = self
            .binder_infos(name)
            .first()
            .is_none_or(|info| *info == BinderInfo::Default);
        if explicit {
            self.display_name(name)
        } else {
            format!("@{}", self.display_name(name))
        }
    }

    /// One group of binders for a dependent `∀`/`→`, as the pin groups them. `hidden`
    /// omits an instance binder's name: the pin does when the name is not accessible and
    /// the body does not use it.
    ///
    /// Each bracketed binder is `ppGroup` (`fill (nest 2 …)`, vendored
    /// `Parser/Term/Basic.lean`): names separated by lines, then `" :"`, a line and the type.
    fn binder_group(
        &self,
        info: BinderInfo,
        names: &[String],
        type_: Format,
        hidden: bool,
    ) -> Format {
        let (open, close) = match info {
            BinderInfo::Implicit => ("{", "}"),
            BinderInfo::StrictImplicit => ("⦃", "⦄"),
            BinderInfo::InstImplicit => ("[", "]"),
            BinderInfo::Default => ("(", ")"),
        };
        if info == BinderInfo::InstImplicit && hidden {
            return node(Format::text(open).then(type_).then(Format::text(close)));
        }
        let mut doc = Format::text(open);
        for (index, name) in names.iter().enumerate() {
            if index > 0 {
                doc = doc.then(Format::Line);
            }
            doc = doc.then(Format::text(name.clone()));
        }
        node(
            doc.then(Format::text(" :"))
                .then(Format::Line)
                .then(type_)
                .then(Format::text(close)),
        )
    }

    /// The name the pin's delaborator gives a bound binder (`getUnusedName`, vendored
    /// `PrettyPrinter/Delaborator/Basic.lean:289-312`). An anonymous binder is `a` and a
    /// macro-scoped name loses its scopes. A name already in scope is kept when `body` does
    /// not refer to the binder it would shadow (`pp.safeShadowing`); otherwise it takes the
    /// first free `_i` suffix (`LocalContext.getUnusedName`). This engine's generated
    /// `_fln…` names record no base name, so they keep printing as `x✝`.
    fn bound_name(&self, name: &Name, body: &Expr) -> String {
        let base = if name.is_anonymous() {
            "a".to_owned()
        } else if name.has_macro_scopes() {
            escaped_name(&name.erase_macro_scopes())
        } else if accessible(name) {
            escaped_name(name)
        } else {
            return binder_name(name);
        };
        let depth = self.names.len();
        let shadows_a_used_binder = self.names.iter().enumerate().any(|(position, shown)| {
            *shown == base
                && body.has_loose_bvar(u32::try_from(depth - position).unwrap_or(u32::MAX))
        });
        if !shadows_a_used_binder {
            return base;
        }
        (1u64..)
            .map(|i| format!("{base}_{i}"))
            .find(|candidate| !self.names.contains(candidate))
            .unwrap_or(base)
    }

    /// A signature parameter's name: as written, or sanitized when inaccessible. The pin's
    /// `sanitizeNames` shows a macro-scoped `a` as `a✝`, and repeats of one base as `a✝¹`,
    /// `a✝²`, ….
    fn parameter_name(&self, name: &Name) -> String {
        if accessible(name) || !name.has_macro_scopes() {
            return binder_name(name);
        }
        let stem = format!("{}✝", escaped_name(&name.erase_macro_scopes()));
        let repeats = self
            .names
            .iter()
            .filter(|shown| {
                shown
                    .strip_prefix(stem.as_str())
                    .is_some_and(|rest| rest.chars().all(|c| SUPERSCRIPTS.contains(c)))
            })
            .count();
        if repeats == 0 {
            stem
        } else {
            let digits: String = repeats
                .to_string()
                .chars()
                .filter_map(|digit| {
                    digit
                        .to_digit(10)
                        .and_then(|d| SUPERSCRIPTS.chars().nth(d as usize))
                })
                .collect();
            format!("{stem}{digits}")
        }
    }

    /// A binder type printed flat, to compare it with a neighbour's for grouping.
    fn flat_type(&mut self, e: &Expr) -> Option<String> {
        self.doc(e, 0).ok().map(|doc| flat(&doc))
    }

    fn pi(&mut self, e: &Expr, outer: u32) -> Doc {
        let ExprNode::ForallE {
            binder_name: name,
            binder_type,
            body,
            binder_info,
        } = e.node()
        else {
            unreachable!("pi called on a pi")
        };
        let dependent = body.has_loose_bvar(0);
        // A non-dependent explicit binder is an arrow (or an implication): `arrow` is
        // `term " → " term`, the token's trailing space a line.
        if !dependent && *binder_info == BinderInfo::Default {
            let domain = self.doc(binder_type, ARROW_PREC + 1)?;
            let shown = self.bound_name(name, body);
            let depth = self.names.len();
            self.bind(shown, binder_type);
            let codomain = self.doc(body, ARROW_PREC);
            self.unbind_to(depth);
            return Ok(paren_doc(
                node(
                    domain
                        .then(Format::text(" →"))
                        .then(Format::Line)
                        .then(codomain?),
                ),
                ARROW_PREC,
                outer,
            ));
        }
        let proposition = self.is_prop(e);
        // Group consecutive binders with one type and one binder kind.
        let depth = self.names.len();
        let mut groups: Vec<Format> = Vec::new();
        let mut current = e;
        let result = loop {
            let ExprNode::ForallE {
                binder_name: name,
                binder_type,
                body,
                binder_info,
            } = current.node()
            else {
                break self.doc(current, ARROW_PREC);
            };
            let dependent = body.has_loose_bvar(0);
            if !dependent && *binder_info == BinderInfo::Default {
                break self.pi(current, ARROW_PREC);
            }
            let type_doc = self.doc(binder_type, 0)?;
            let type_text = flat(&type_doc);
            let hidden = !dependent && !accessible(name);
            let mut names = vec![self.bound_name(name, body)];
            self.bind(names[0].clone(), binder_type);
            let mut next = body;
            // The pin groups a following binder with the same kind and the same type.
            while let ExprNode::ForallE {
                binder_name: other,
                binder_type: other_type,
                body: other_body,
                binder_info: other_info,
            } = next.node()
            {
                if other_info != binder_info || !other_body.has_loose_bvar(0) {
                    break;
                }
                let same = !other_type.has_loose_bvar(0)
                    && self.flat_type(other_type) == Some(type_text.clone());
                if !same || proposition && *binder_info == BinderInfo::InstImplicit {
                    break;
                }
                let shown = self.bound_name(other, other_body);
                names.push(shown.clone());
                self.bind(shown, other_type);
                next = other_body;
            }
            groups.push(self.binder_group(*binder_info, &names, type_doc, hidden));
            current = next;
            if proposition {
                // `∀ (x : A) (y : B), p` keeps collecting dependent binders.
                continue;
            }
            // `(x : A) → B`: `depArrow` is `bracketedBinder " → " term`.
            let rest = self.pi_tail(current);
            self.unbind_to(depth);
            let group = groups.pop().expect("one binder group");
            return Ok(paren_doc(
                node(
                    group
                        .then(Format::text(" →"))
                        .then(Format::Line)
                        .then(rest?),
                ),
                ARROW_PREC,
                outer,
            ));
        };
        self.unbind_to(depth);
        let body = result?;
        // `∀` ++ (ppSpace binder)* ++ ", " ++ term (vendored `Parser/Term.lean`, `forall`).
        let mut doc = Format::text("∀");
        for group in groups {
            doc = doc.then(Format::Line).then(group);
        }
        // A trailing `∀` needs no parentheses as an arrow's codomain (the pin prints
        // `… → ∀ {a : Nat} (t : Q a), motive a t`), only where something tighter encloses it:
        // an arrow's domain or an argument.
        Ok(paren_doc(
            node(doc.then(Format::text(",")).then(Format::Line).then(body)),
            ARROW_PREC,
            outer,
        ))
    }

    fn pi_tail(&mut self, e: &Expr) -> Doc {
        self.doc(e, ARROW_PREC)
    }

    /// `#check c` for a constant: `c binders : type` (`delabConstWithSignature`), the
    /// leading binders with accessible names shown before the colon, grouped.
    pub fn signature(&mut self, name: &Name, type_: &Expr) -> Printed {
        let mut groups = Vec::new();
        let mut current = type_;
        let depth = self.names.len();
        let mut used: Vec<Name> = Vec::new();
        while let ExprNode::ForallE {
            binder_name: binder,
            binder_type,
            body,
            binder_info,
        } = current.node()
        {
            // `delabParams`: a non-dependent binder whose name is inaccessible or already used
            // ends the parameters; the rest is the type after the colon. A dependent one stays,
            // under its sanitized name (`a✝`, `a✝¹`, …).
            let ends = |name: &Name, body: &Expr, used: &[Name]| {
                !body.has_loose_bvar(0) && (!accessible(name) || used.contains(name))
            };
            if *binder_info != BinderInfo::InstImplicit && ends(binder, body, &used) {
                break;
            }
            used.push(binder.clone());
            let type_doc = self.doc(binder_type, 0)?;
            let type_text = flat(&type_doc);
            let mut names = vec![self.parameter_name(binder)];
            self.bind(names[0].clone(), binder_type);
            let mut next = body;
            // `shouldGroupWithNext`: same binder style and domain, never an instance, and the
            // next binder would itself stay a parameter.
            while let ExprNode::ForallE {
                binder_name: other,
                binder_type: other_type,
                body: other_body,
                binder_info: other_info,
            } = next.node()
            {
                if other_info != binder_info
                    || *other_info == BinderInfo::InstImplicit
                    || ends(other, other_body, &used)
                    || other_type.has_loose_bvar(0)
                    || self.flat_type(other_type) != Some(type_text.clone())
                {
                    break;
                }
                used.push(other.clone());
                let shown = self.parameter_name(other);
                names.push(shown.clone());
                self.bind(shown, other_type);
                next = other_body;
            }
            let hidden = !accessible(binder);
            groups.push(self.binder_group(*binder_info, &names, type_doc, hidden));
            current = next;
        }
        let rest = self.doc(current, 0);
        self.unbind_to(depth);
        // The signature names the constant's universe parameters (`List.map.{u_1, u_2}`).
        let parameters = self
            .env
            .find(name)
            .map(|info| info.constant_val().level_params.clone())
            .unwrap_or_default();
        let head = if parameters.is_empty() {
            self.display_name(name)
        } else {
            format!(
                "{}.{{{}}}",
                self.display_name(name),
                parameters
                    .iter()
                    .map(escaped_name)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        // `declSigWithId`, formatted as a term (`ppSignature`'s `ppTerm`): one
        // `fill (nest 2 …)` holding the name, a line before each binder group, then
        // `typeSpec`'s `" :"`, a line and the type.
        let mut doc = Format::text(head);
        for group in groups {
            doc = doc.then(Format::Line).then(group);
        }
        Ok(node(doc.then(Format::text(" :")).then(Format::Line).then(rest?)).pretty(WIDTH))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(parts: &[&str]) -> Name {
        Name::from_components(parts.iter().copied())
    }

    /// Each expected string is the pinned v4.32.0's `#check` output for a constant of that
    /// name (measured 2026-10-09), except the pseudo-syntax and inaccessible rows, which
    /// follow `toStringWithToken`'s documented exclusions.
    #[test]
    fn names_are_escaped_as_the_pin_prints_them() {
        for (parts, expected) in [
            (&["Nat", "succ"][..], "Nat.succ"),
            (&["Foo", "a b"][..], "Foo.«a b»"),
            (&["Minus", "i-love-lisp"][..], "Minus.«i-love-lisp»"),
            (&["fun"][..], "«fun»"),
            (&["def", "x"][..], "«def».x"),
            (&["α"][..], "α"),
            (&["x✝"][..], "x✝"),
            (&["_"][..], "_"),
            (&["?u"][..], "?u"),
            (&["a»b"][..], "a»b"),
        ] {
            assert_eq!(escaped_name(&name(parts)), expected, "{parts:?}");
        }
        assert_eq!(
            escaped_name(&Name::num(name(&["Foo"]), 1)),
            "Foo.1",
            "a numeric component is its digits"
        );
        assert_eq!(escaped_part("i-love-lisp", false), "«i-love-lisp»");
        assert_eq!(escaped_part("ok", true), "«ok»");
    }

    /// Bound binder names as the pin's `getUnusedName` gives them. The pin prints
    /// `@G.rec : {a : Nat} → {motive : (a_1 : Nat) → G a a_1 → Sort u_1} → …` for
    /// `inductive G : Nat → Nat → Type | mk (n : Nat) : G n 0`, whose binders are both the
    /// arrow's `a._@._internal._hyg.0`; `fun (x : Nat) (x : Nat) => …` keeps both names
    /// unless the body uses the outer one.
    #[test]
    fn bound_names_lose_their_scopes_and_avoid_shadowing_a_used_binder() {
        let env = Environment::new();
        let nat = || Expr::const_(name(&["Nat"]), Vec::new());
        let var = |i| Expr::bvar(i).unwrap();
        let arrow = Name::num(name(&["a", "_@", "_internal", "_hyg"]), 0);
        let g = Expr::app(
            Expr::app(Expr::const_(name(&["G"]), Vec::new()), var(1)),
            var(0),
        );
        let telescope = Expr::forall_e(
            arrow.clone(),
            nat(),
            Expr::forall_e(arrow, nat(), g, BinderInfo::Default),
            BinderInfo::Implicit,
        );
        let mut printer = Printer::new(&env);
        assert_eq!(
            printer.expr(&telescope, 0).unwrap(),
            "{a : Nat} → (a_1 : Nat) → G a a_1"
        );
        let anonymous = Expr::forall_e(
            Name::anonymous(),
            nat(),
            Expr::app(Expr::const_(name(&["P"]), Vec::new()), var(0)),
            BinderInfo::Default,
        );
        assert_eq!(printer.expr(&anonymous, 0).unwrap(), "(a : Nat) → P a");
        let x = || name(&["x"]);
        let shadowing = |body: Expr| {
            Expr::lam(
                x(),
                nat(),
                Expr::lam(x(), nat(), body, BinderInfo::Default),
                BinderInfo::Default,
            )
        };
        assert_eq!(printer.expr(&shadowing(var(0)), 0).unwrap(), "fun x x => x");
        assert_eq!(
            printer.expr(&shadowing(var(1)), 0).unwrap(),
            "fun x x_1 => x"
        );
    }

    /// A `∀` whose body's head is a bound motive into `Prop` is a proposition. At the pin,
    /// `axiom fooAx : ∀ {motive : Nat → Prop} (n : Nat), motive n` prints as written, and
    /// a non-dependent proof binder is an arrow: `∀ {motive : Nat → Prop}, (∀ (n : Nat),
    /// motive n) → motive 0`. A proof that is not atomic is `⋯` inside a term that is not
    /// itself a proof (`@P.rec : … → motive ⋯ → …` at the pin).
    #[test]
    fn a_motive_headed_body_is_a_proposition_and_proofs_inside_terms_are_omitted() {
        let env = Environment::new();
        let nat = || Expr::const_(name(&["Nat"]), Vec::new());
        let var = |i| Expr::bvar(i).unwrap();
        let zero = || Expr::lit(Literal::Nat(NatLit::from_u64(0)));
        let motive_type = || {
            Expr::forall_e(
                Name::anonymous(),
                nat(),
                Expr::sort(Level::zero()),
                BinderInfo::Default,
            )
        };
        let every = |body: Expr| Expr::forall_e(name(&["n"]), nat(), body, BinderInfo::Default);
        let foo = Expr::forall_e(
            name(&["motive"]),
            motive_type(),
            every(Expr::app(var(1), var(0))),
            BinderInfo::Implicit,
        );
        let mut printer = Printer::new(&env);
        assert_eq!(
            printer.expr(&foo, 0).unwrap(),
            "∀ {motive : Nat → Prop} (n : Nat), motive n"
        );
        let baz = Expr::forall_e(
            name(&["motive"]),
            motive_type(),
            Expr::forall_e(
                name(&["f"]),
                every(Expr::app(var(1), var(0))),
                Expr::app(var(1), zero()),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        );
        assert_eq!(
            printer.expr(&baz, 0).unwrap(),
            "∀ {motive : Nat → Prop}, (∀ (n : Nat), motive n) → motive 0"
        );
        // `{motive : Nat → Prop} → (f : ∀ (n : Nat), motive n) → R (f 0)`: `f 0` is a proof.
        let omitted = Expr::forall_e(
            name(&["motive"]),
            motive_type(),
            Expr::forall_e(
                name(&["f"]),
                every(Expr::app(var(1), var(0))),
                Expr::app(
                    Expr::const_(name(&["R"]), Vec::new()),
                    Expr::app(var(0), zero()),
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        );
        assert_eq!(
            printer.expr(&omitted, 0).unwrap(),
            "{motive : Nat → Prop} → (f : ∀ (n : Nat), motive n) → R ⋯"
        );
    }
}
