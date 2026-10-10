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
//! Anything else is reported as unsupported rather than printed differently: a caller
//! must not show text the pin would not show.
use super::*;
use fln_core::expr::NatLit;
use fln_core::level::LevelView;

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

fn parens(text: String, inner: u32, outer: u32) -> String {
    if inner < outer {
        format!("({text})")
    } else {
        text
    }
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
/// names of the binders in scope (innermost last).
pub struct Printer<'a> {
    env: &'a Environment,
    scope: Option<&'a fln_elab::source::scope::SourceScope>,
    names: Vec<String>,
    budget: usize,
}

impl<'a> Printer<'a> {
    pub fn new(env: &'a Environment) -> Self {
        Self {
            env,
            scope: None,
            names: Vec::new(),
            budget: 100_000,
        }
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

    /// Whether a constant's type ends in `Prop` (so an application of it is a
    /// proposition).
    fn returns_prop(&self, name: &Name) -> bool {
        let Some(info) = self.env.find(name) else {
            return false;
        };
        let mut type_ = &info.constant_val().type_;
        while let ExprNode::ForallE { body, .. } = type_.node() {
            type_ = body;
        }
        matches!(type_.node(), ExprNode::Sort { level } if level.is_zero())
    }

    /// Whether `e` is (syntactically) a proposition: a sort-`Prop` application, a
    /// connective, or a `∀` into one.
    fn is_prop(&self, e: &Expr) -> bool {
        let mut e = e;
        loop {
            match e.node() {
                ExprNode::ForallE { body, .. } => e = body,
                ExprNode::MData { expr, .. } => e = expr,
                _ => break,
            }
        }
        let (head, _) = spine(e);
        match head.node() {
            ExprNode::Const { name, .. } => self.returns_prop(name),
            _ => false,
        }
    }

    pub fn expr(&mut self, e: &Expr, outer: u32) -> Printed {
        self.tick()?;
        match e.node() {
            ExprNode::BVar { idx } => {
                let idx = usize::try_from(*idx).unwrap_or(usize::MAX);
                self.names
                    .len()
                    .checked_sub(idx + 1)
                    .and_then(|at| self.names.get(at))
                    .cloned()
                    .ok_or(Unsupported("a loose bound variable"))
            }
            ExprNode::FVar { .. } => Err(Unsupported("a free variable")),
            ExprNode::MVar { .. } => Err(Unsupported("a metavariable")),
            ExprNode::Sort { level } => {
                let text = sort(level)?;
                let atomic = !text.contains(' ');
                Ok(if atomic {
                    text
                } else {
                    parens(text, MAX_PREC - 1, outer)
                })
            }
            ExprNode::Const { name, .. } => Ok(self.constant(name)),
            ExprNode::Lit { literal } => Ok(match literal {
                Literal::Nat(value) => nat_decimal(value),
                Literal::Str(text) => string_literal(text),
            }),
            ExprNode::MData { expr, .. } => self.expr(expr, outer),
            ExprNode::App { .. } => self.application(e, outer),
            ExprNode::ForallE { .. } => self.pi(e, outer),
            ExprNode::Lam { .. } => {
                let mut binders = Vec::new();
                let mut body = e;
                let depth = self.names.len();
                while let ExprNode::Lam {
                    binder_name: name,
                    body: inner,
                    ..
                } = body.node()
                {
                    let shown = binder_name(name);
                    binders.push(shown.clone());
                    self.names.push(shown);
                    body = inner;
                }
                let printed = self.expr(body, 0);
                self.names.truncate(depth);
                Ok(parens(
                    format!("fun {} => {}", binders.join(" "), printed?),
                    0,
                    outer,
                ))
            }
            // `let x : T := v; x` is how a type ascription `(v : T)` elaborates here; the
            // pin's term is `v` itself.
            ExprNode::LetE { value, body, .. }
                if matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
            {
                self.expr(value, outer)
            }
            // At the top of the printed term the pin breaks a `let` after its `;` with no
            // indentation; nested inside another construct it indents by the enclosing
            // group's width, which is not reproduced.
            ExprNode::LetE {
                decl_name: name,
                value,
                body,
                ..
            } if outer == 0 && self.names.is_empty() => {
                let value = self.expr(value, 0)?;
                let shown = binder_name(name);
                self.names.push(shown.clone());
                let printed = self.expr(body, 0);
                self.names.pop();
                Ok(format!("let {shown} := {value};\n{}", printed?))
            }
            ExprNode::LetE { .. } => Err(Unsupported("a nested let expression")),
            ExprNode::Proj { idx, expr, .. } => {
                Ok(format!("{}.{}", self.expr(expr, MAX_PREC)?, idx + 1))
            }
        }
    }

    fn application(&mut self, e: &Expr, outer: u32) -> Printed {
        let (head, args) = spine(e);
        if let ExprNode::Const { name, .. } = head.node() {
            let text = name.to_display_string();
            if text == "OfNat.ofNat"
                && args.len() == 3
                && let ExprNode::Lit {
                    literal: Literal::Nat(value),
                } = args[1].node()
            {
                return Ok(nat_decimal(value));
            }
            // `notation:max "¬" p:40 => Not p`.
            if text == "Not" && args.len() == 1 {
                return Ok(parens(
                    format!("¬{}", self.expr(&args[0], 40)?),
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
                        let mut shown = Vec::with_capacity(elements.len());
                        for element in &elements {
                            shown.push(self.expr(element, 0)?);
                        }
                        return Ok(format!("[{}]", shown.join(", ")));
                    }
                    break;
                }
            }
            if text == "List.nil" && args.len() == 1 {
                return Ok("[]".to_owned());
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
                let lhs = self.expr(&args[args.len() - 2], lhs_prec)?;
                let rhs = self.expr(&args[args.len() - 1], rhs_prec)?;
                return Ok(parens(
                    format!("{lhs} {} {rhs}", infix.symbol),
                    infix.precedence,
                    outer,
                ));
            }
            let infos = self.binder_infos(name);
            // Generalized field notation: `C.f r …` is `r.f …` when `r` is `C.f`'s first
            // explicit argument and has type `C …` (never on a numeric literal).
            if let Some((receiver, field)) = self.field_receiver(name, &infos, &args) {
                let mut shown = vec![format!("{}.{field}", self.expr(&args[receiver], MAX_PREC)?)];
                for (index, arg) in args.iter().enumerate() {
                    let explicit = infos
                        .get(index)
                        .is_none_or(|info| *info == BinderInfo::Default);
                    if explicit && index != receiver {
                        shown.push(self.expr(arg, MAX_PREC)?);
                    }
                }
                return Ok(if shown.len() == 1 {
                    shown.remove(0)
                } else {
                    parens(shown.join(" "), MAX_PREC - 1, outer)
                });
            }
            let mut shown = Vec::new();
            for (index, arg) in args.iter().enumerate() {
                let explicit = infos
                    .get(index)
                    .is_none_or(|info| *info == BinderInfo::Default);
                if explicit {
                    shown.push(self.expr(arg, MAX_PREC)?);
                }
            }
            let text = self.display_name(name);
            if shown.is_empty() {
                return Ok(text);
            }
            return Ok(parens(
                format!("{text} {}", shown.join(" ")),
                MAX_PREC - 1,
                outer,
            ));
        }
        let mut shown = vec![self.expr(&head, MAX_PREC)?];
        for arg in &args {
            shown.push(self.expr(arg, MAX_PREC)?);
        }
        Ok(parens(shown.join(" "), MAX_PREC - 1, outer))
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

    /// One group of binders for a dependent `∀`/`→`, as the pin groups them.
    fn binder_group(&self, info: BinderInfo, names: &[String], type_: &str) -> String {
        match info {
            BinderInfo::Implicit => format!("{{{} : {type_}}}", names.join(" ")),
            BinderInfo::StrictImplicit => format!("⦃{} : {type_}⦄", names.join(" ")),
            BinderInfo::InstImplicit => {
                if names.iter().all(|name| name.ends_with('✝')) {
                    format!("[{type_}]")
                } else {
                    format!("[{} : {type_}]", names.join(" "))
                }
            }
            BinderInfo::Default => format!("({} : {type_})", names.join(" ")),
        }
    }

    fn pi(&mut self, e: &Expr, outer: u32) -> Printed {
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
        // A non-dependent explicit binder is an arrow (or an implication).
        if !dependent && *binder_info == BinderInfo::Default {
            let domain = self.expr(binder_type, ARROW_PREC + 1)?;
            self.names.push(binder_name(name));
            let codomain = self.expr(body, ARROW_PREC);
            self.names.pop();
            return Ok(parens(
                format!("{domain} → {}", codomain?),
                ARROW_PREC,
                outer,
            ));
        }
        let proposition = self.is_prop(e);
        // Group consecutive binders with one type and one binder kind.
        let depth = self.names.len();
        let mut groups: Vec<String> = Vec::new();
        let mut current = e;
        let result = loop {
            let ExprNode::ForallE {
                binder_name: name,
                binder_type,
                body,
                binder_info,
            } = current.node()
            else {
                break self.expr(current, ARROW_PREC);
            };
            let dependent = body.has_loose_bvar(0);
            if !dependent && *binder_info == BinderInfo::Default {
                break self.pi(current, ARROW_PREC);
            }
            let type_text = self.expr(binder_type, 0)?;
            let mut names = vec![binder_name(name)];
            self.names.push(names[0].clone());
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
                    && self.expr(other_type, 0).ok() == Some(type_text.clone());
                if !same || proposition && *binder_info == BinderInfo::InstImplicit {
                    break;
                }
                let shown = binder_name(other);
                names.push(shown.clone());
                self.names.push(shown);
                next = other_body;
            }
            if proposition && *binder_info == BinderInfo::Default {
                groups.push(format!("({} : {type_text})", names.join(" ")));
            } else {
                groups.push(self.binder_group(*binder_info, &names, &type_text));
            }
            current = next;
            if proposition {
                // `∀ (x : A) (y : B), p` keeps collecting dependent binders.
                continue;
            }
            // `(x : A) → B`: each group is its own arrow.
            let rest = self.pi_tail(current);
            self.names.truncate(depth);
            return Ok(parens(
                format!("{} → {}", groups.join(" → "), rest?),
                ARROW_PREC,
                outer,
            ));
        };
        self.names.truncate(depth);
        let body = result?;
        Ok(parens(format!("∀ {}, {body}", groups.join(" ")), 0, outer))
    }

    fn pi_tail(&mut self, e: &Expr) -> Printed {
        self.expr(e, ARROW_PREC)
    }

    /// `#check c` for a constant: `c binders : type` (`delabConstWithSignature`), the
    /// leading binders with accessible names shown before the colon, grouped.
    pub fn signature(&mut self, name: &Name, type_: &Expr) -> Printed {
        let mut groups = Vec::new();
        let mut current = type_;
        let depth = self.names.len();
        while let ExprNode::ForallE {
            binder_name: binder,
            binder_type,
            body,
            binder_info,
        } = current.node()
        {
            if !accessible(binder) && *binder_info != BinderInfo::InstImplicit {
                break;
            }
            let type_text = self.expr(binder_type, 0)?;
            let mut names = vec![binder_name(binder)];
            self.names.push(names[0].clone());
            let mut next = body;
            while let ExprNode::ForallE {
                binder_name: other,
                binder_type: other_type,
                body: other_body,
                binder_info: other_info,
            } = next.node()
            {
                if other_info != binder_info
                    || !accessible(other)
                    || other_type.has_loose_bvar(0)
                    || self.expr(other_type, 0).ok() != Some(type_text.clone())
                {
                    break;
                }
                let shown = binder_name(other);
                names.push(shown.clone());
                self.names.push(shown);
                next = other_body;
            }
            groups.push(self.binder_group(*binder_info, &names, &type_text));
            current = next;
        }
        let rest = self.expr(current, 0);
        self.names.truncate(depth);
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
        Ok(if groups.is_empty() {
            format!("{head} : {}", rest?)
        } else {
            format!("{head} {} : {}", groups.join(" "), rest?)
        })
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
}
