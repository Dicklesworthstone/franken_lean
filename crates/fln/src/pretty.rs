//! A bounded delaborator: kernel terms printed as the pin's `lean` prints them for
//! `#check` (`Lean.PrettyPrinter.Delaborator`), under the pretty-printer options of the
//! printing scope ([`PpOptions`]: `pp.explicit`, `pp.universes`, `pp.notation`, `pp.all` and
//! the others the pin's delaborator reads).
//!
//! Covered: constants and universe levels (`Type u_1`, `Sort (max u v)`), applications
//! with implicit and instance arguments hidden (`pp.explicit false`) or shown in explicit mode,
//! the arithmetic, relation and connective notations of `Init` (with their precedences and
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
pub mod goals;
mod notations;
mod options;
mod print;
mod structures;
use format::Format;
pub use options::PpOptions;

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
    // `infix:50 " != " => bne` (`Init/Core.lean`).
    Infix {
        function: "bne",
        arity: 4,
        symbol: "!=",
        precedence: 50,
        right: false,
    },
    // `infixl:35 " && " => and`, `infixl:30 " || " => or` (`Init/Notation.lean`), whose
    // `and`/`or` are `Bool.and`/`Bool.or` through `export Bool (or and not)`.
    Infix {
        function: "Bool.and",
        arity: 2,
        symbol: "&&",
        precedence: 35,
        right: false,
    },
    Infix {
        function: "Bool.or",
        arity: 2,
        symbol: "||",
        precedence: 30,
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
    // `infixr:90 " ∘ " => Function.comp` (`Init/Notation.lean:272`).
    Infix {
        function: "Function.comp",
        arity: 5,
        symbol: "∘",
        precedence: 90,
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
/// `let`, or `have` for a nondependent binding (`let +nondep`), as the pin prints each.
/// How a dependent `let` prints: as itself, or as `#print` shows a definition's value after the
/// pin's `letToHave` cleanup (vendored `Lean/Elab/PreDefinition/Basic.lean:96-108`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LetMode {
    AsIs,
    /// The value is a safe definition's whose type is not a proposition: the pin has turned
    /// each nondependent `let` into `have`. One whose body never uses its variable is
    /// certainly nondependent; for any other this door does not decide dependence.
    ToHave,
    /// The value may have had `letToHave` applied or not: no `let` prints.
    Refuse,
}

fn let_keyword(non_dep: bool) -> &'static str {
    if non_dep { "have" } else { "let" }
}

fn strip_mdata(mut e: &Expr) -> &Expr {
    while let ExprNode::MData { expr, .. } = e.node() {
        e = expr;
    }
    e
}

/// `Core.betaReduce` (vendored `Lean/Meta/Transform.lean:75-76`): every subterm that is a
/// `fun` applied to arguments (`isHeadBetaTarget`, looking through annotations on the
/// function) is replaced by its `headBeta`, and the result visited again.
fn beta_reduce(e: &Expr) -> Result<Expr, Unsupported> {
    let too_many = |_| Unsupported("a term with too many bound variables to reduce");
    let (head, args) = spine(e);
    if !args.is_empty() && matches!(strip_mdata(&head).node(), ExprNode::Lam { .. }) {
        // `betaRev`: consume as many `fun`s as there are arguments, then apply the rest.
        let mut body = strip_mdata(&head).clone();
        let mut taken = 0;
        while taken < args.len()
            && let ExprNode::Lam { body: inner, .. } = strip_mdata(&body).node()
        {
            body = inner.clone();
            taken += 1;
        }
        let substs: Vec<Expr> = args[..taken].to_vec();
        let mut reduced = body.subst_loose(0, &substs).map_err(too_many)?;
        for arg in &args[taken..] {
            reduced = Expr::app(reduced, arg.clone());
        }
        return beta_reduce(&reduced);
    }
    Ok(match e.node() {
        ExprNode::App { f, a } => Expr::app(beta_reduce(f)?, beta_reduce(a)?),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            beta_reduce(binder_type)?,
            beta_reduce(body)?,
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            beta_reduce(binder_type)?,
            beta_reduce(body)?,
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            beta_reduce(type_)?,
            beta_reduce(value)?,
            beta_reduce(body)?,
            *non_dep,
        ),
        ExprNode::MData { data, expr } => Expr::mdata(data.clone(), beta_reduce(expr)?),
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => Expr::proj(struct_name.clone(), *idx, beta_reduce(expr)?),
        _ => e.clone(),
    })
}

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

/// `delabOfScientific`'s literal for `OfScientific.ofScientific mantissa negative exponent`:
/// a decimal point inside the digits, `0.` before them all, or an exponent.
fn scientific(digits: &str, negative: bool, exponent: &str) -> String {
    let places = exponent.parse::<usize>().ok();
    match places {
        Some(places) if negative && places == digits.len() => format!("0.{digits}"),
        Some(places) if negative && places < digits.len() => {
            let (whole, fraction) = digits.split_at(digits.len() - places);
            format!("{whole}.{fraction}")
        }
        _ => format!("{digits}e{}{exponent}", if negative { "-" } else { "" }),
    }
}

/// `Char.quote` (vendored `Init/Data/Repr.lean:360-374`): `'c'`, with `\n`, `\t`, `\\`, `\"`,
/// `\'` and `\xNN` below 32 and for DEL.
fn char_literal(c: char) -> String {
    let inner = match c {
        '\n' => "\\n".to_owned(),
        '\t' => "\\t".to_owned(),
        '\\' => "\\\\".to_owned(),
        '"' => "\\\"".to_owned(),
        '\'' => "\\'".to_owned(),
        c if (c as u32) <= 31 || c == '\x7f' => format!("\\x{:02x}", c as u32),
        c => c.to_string(),
    };
    format!("'{inner}'")
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
    escaped_name_with(name, is_token)
}

/// A name as the pin's `Name.toString` prints it, which no token forces to escape: the
/// form `m!"{n}"` gives a name in a message (`MessageData.ofName`, vendored
/// `src/Lean/Message.lean:276`; `Init/Data/ToString/Name.lean:123`).
pub(crate) fn message_name(name: &Name) -> String {
    escaped_name_with(name, |_| false)
}

/// [`escaped_name`] with `is_token` deciding which names read as tokens.
fn escaped_name_with(name: &Name, is_token: impl Fn(&str) -> bool) -> String {
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

/// Whether `e` is a numeral, `@OfNat.ofNat _ n _` of a raw literal (`delabOfNatCore`'s match).
fn ofnat_literal(e: &Expr) -> bool {
    let (head, args) = spine(e);
    matches!(head.node(), ExprNode::Const { name, .. } if name.to_display_string() == "OfNat.ofNat")
        && args.len() == 3
        && matches!(
            args[1].node(),
            ExprNode::Lit {
                literal: Literal::Nat(_)
            }
        )
}

/// Whether `name` is private (`isPrivateName`): its root component is `_private`.
pub(crate) fn is_private(name: &Name) -> bool {
    let mut root = name.clone();
    while !root.parent().is_anonymous() {
        root = root.parent();
    }
    root.leaf_view() == LeafView::Str("_private")
}

/// Whether `name` is a binder this engine's elaboration introduced (`_fln…`, or named by a
/// number), which the pin's term never has. The first component decides: a hygienic
/// `x._@.M._hyg.4` is the user's `x`.
pub(crate) fn internal_name(name: &Name) -> bool {
    let mut first = name.clone();
    while !first.parent().is_anonymous() {
        first = first.parent();
    }
    match first.leaf_view() {
        LeafView::Str(text) => text.starts_with("_fln"),
        LeafView::Num(_) => true,
        LeafView::Anonymous => false,
    }
}

const INTERNAL_BINDER: Unsupported =
    Unsupported("a binder this engine's elaboration introduced (a compiled `if` or `match`)");

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
    /// What name unresolution reads, with a scope: `None` without one, or when a journal
    /// cannot be read, and then names print in full.
    resolution: Option<Resolution>,
    /// Whether a trailing parser follows the term being printed at its level: an infix's
    /// left operand, an arrow's domain. The pin's parenthesizer brackets a notation whose
    /// body extends to the right (`∃ x, p`) there, where the body would absorb it, and as
    /// an argument.
    trailing: bool,
    /// How many binders the top of the printed term sits under: the section variables a
    /// `#check` opens, then each `let` of a chain at the top. A `let` there breaks after its `;`.
    top_names: usize,
    /// The source's own notations in force ([`notations`]).
    notations: Option<&'a fln_parse::extensions::Notations>,
    /// How a dependent `let` prints ([`LetMode`]).
    lets: LetMode,
    /// The imported delaborator tags (`pp_using_anonymous_constructor`, `pp_nodot`,
    /// `app_unexpander` keys), or `None` when the journal cannot be read.
    tags: Option<fln_elab::delaborator_tags::DelaboratorTags>,
    /// Whether the environment records imported delaborator tags at all: importing any `Init`
    /// module does (`Init.Prelude` tags `Subtype`). Without them, as in the native source
    /// profile, the `Init.NotationExtra` unexpanders this printer reproduces are assumed.
    imported_tags: bool,
    /// Structure metadata, read when a structure instance is first printed.
    structures: Option<structures::StructureTables>,
    /// The next `∀` printed is on the spine of a signature's type after its colon, where the
    /// pin shows every accessible binder name (`pp.piBinderNames`, set by `processSpine`,
    /// vendored `PrettyPrinter/Delaborator/Builtins.lean:1644-1660`). Taken by [`Printer::pi`].
    spine_names: bool,
    /// The pin's pretty-printer options in force ([`PpOptions`]): the scope's, or the defaults.
    pp: PpOptions,
    /// For each binder in scope (as [`Printer::names`]), whether the term printed under it so
    /// far has shown its name: the pin's `stxBody.raw.hasIdent`, which decides whether an
    /// instance binder of a `fun` is named.
    shown: Vec<bool>,
}

/// A function parameter as the pin's `getParamKinds` records it (vendored
/// `PrettyPrinter/Delaborator/Builtins.lean:160-213`).
struct ParamKind {
    info: BinderInfo,
    /// Whether the domain is an `optParam`.
    optional: bool,
    /// For a parameter an argument supplies, its `optParam` default instantiated with the
    /// universe levels and the arguments before it.
    default: Option<Expr>,
    /// Whether the domain is an `autoParam`.
    auto: bool,
}

impl ParamKind {
    /// `ParamKind.isRegularExplicit`: explicit, with neither a default nor a tactic.
    fn regular_explicit(&self) -> bool {
        self.info == BinderInfo::Default && !self.optional && !self.auto
    }
}

/// `e.isAppOfArity gadget 2` for the root type annotation `gadget` (`optParam`, `autoParam`):
/// its type and its default or tactic (`Expr.getOptParamDefault?`, `Expr.isAutoParam`).
fn annotation<'e>(e: &'e Expr, gadget: &str) -> Option<(&'e Expr, &'e Expr)> {
    let ExprNode::App { f, a: value } = e.node() else {
        return None;
    };
    let ExprNode::App { f: head, a: type_ } = f.node() else {
        return None;
    };
    matches!(head.node(), ExprNode::Const { name, .. }
        if name.parent().is_anonymous() && name.leaf_view() == LeafView::Str(gadget))
    .then_some((type_, value))
}

/// `useAppExplicit` under the default options: an application with `count` arguments is
/// printed in explicit mode when the next parameter is implicit or an instance, or a later
/// explicit parameter has a default or a tactic (the elaborator would fill it eagerly).
fn app_explicit(count: usize, kinds: &[ParamKind]) -> bool {
    kinds.len() < count
        || kinds.get(count).is_some_and(|next| {
            matches!(next.info, BinderInfo::Implicit | BinderInfo::InstImplicit)
        })
        || kinds
            .iter()
            .skip(count)
            .any(|kind| kind.info == BinderInfo::Default && !kind.regular_explicit())
}

/// `needsExplicit`: whether explicit mode heads the application with `@`.
fn needs_explicit(count: usize, kinds: &[ParamKind]) -> bool {
    kinds.len() < count
        || kinds
            .iter()
            .take(count)
            .any(|kind| kind.info != BinderInfo::Default)
        || app_explicit(count, kinds)
}

/// How an argument prints in the pin's implicit mode (`AppImplicitArg`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shown {
    Skip,
    Regular,
    /// Equal to its parameter's default: dropped when it, and all after it, are.
    Optional,
}

/// The imported `export` aliases, each declaration's aliases, and the `protected` names: what
/// the pin's `resolveGlobalName` consults, read once per printer.
struct Resolution {
    aliases: fln_elab::aliases::AliasTable,
    reverse: std::collections::BTreeMap<Name, Vec<Name>>,
    protected: fln_elab::protected_names::ProtectedNames,
}

impl Resolution {
    fn read(env: &Environment) -> Option<Self> {
        let aliases = fln_elab::aliases::AliasTable::read(env).ok()?;
        let protected = fln_elab::protected_names::ProtectedNames::read(env).ok()?;
        let mut reverse = std::collections::BTreeMap::<Name, Vec<Name>>::new();
        for (alias, targets) in aliases.entries() {
            for target in targets {
                reverse
                    .entry(target.clone())
                    .or_default()
                    .push(alias.clone());
            }
        }
        Some(Self {
            aliases,
            reverse,
            protected,
        })
    }

    /// The pin's `unresolveNameGlobal` (vendored `Lean/ResolveName.lean`): the shortest suffix
    /// of an `export` alias of `name`, then of `_root_.name`, that resolves to exactly `name` in
    /// `scope`, so `Option.some` prints `some` and, under `open Nat`, `Nat.add` prints `add`.
    /// A name with macro scopes, or one no suffix reaches, keeps its source spelling.
    fn unresolve(
        &self,
        env: &Environment,
        scope: &fln_elab::source::scope::SourceScope,
        name: &Name,
    ) -> Name {
        if name.has_macro_scopes() {
            return scope.user_name(name);
        }
        let root = Name::from_components(["_root_"]).append_core(name);
        let aliases = self.reverse.get(name).map_or(&[][..], Vec::as_slice);
        // Without `allowHorizAliases`, an alias counts only when its namespace
        // encloses the declaration's own (`ResolveName.lean:656-658`): `export
        // Nat (twice)` in `Box` never prints `Nat.twice` as `Box.twice`.
        let namespace = scope.user_name(name).parent();
        let vertical = |alias: &&Name| {
            let prefix = alias.parent();
            let mut cursor = namespace.clone();
            loop {
                if cursor == prefix {
                    return true;
                }
                if cursor.is_anonymous() {
                    return false;
                }
                cursor = cursor.parent();
            }
        };
        for initial in aliases
            .iter()
            .filter(vertical)
            .chain(std::iter::once(&root))
        {
            let mut components = Vec::new();
            let mut cursor = initial.clone();
            while !cursor.is_anonymous() {
                components.push(cursor.clone());
                cursor = cursor.parent();
            }
            // Leaf first: `false`, then `Bool.false`, then `_root_.Bool.false`.
            let mut candidate = Name::anonymous();
            for component in &components {
                let leaf = match component.leaf_view() {
                    LeafView::Str(text) => Name::str(Name::anonymous(), text),
                    LeafView::Num(value) => Name::num(Name::anonymous(), value),
                    LeafView::Anonymous => break,
                };
                candidate = leaf.append_core(&candidate);
                let resolved = scope.resolve_with_aliases(
                    &candidate,
                    |declaration| env.contains(declaration),
                    &self.aliases,
                    &self.protected,
                );
                if matches!(resolved, Ok(Some(found)) if found == *name) {
                    return candidate;
                }
            }
        }
        scope.user_name(name)
    }
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
            resolution: None,
            trailing: false,
            top_names: 0,
            notations: None,
            lets: LetMode::AsIs,
            tags: fln_elab::delaborator_tags::DelaboratorTags::read(env).ok(),
            imported_tags: env
                .extension(&fln_elab::delaborator_tags::journal_name())
                .is_some(),
            structures: None,
            spine_names: false,
            pp: PpOptions::default(),
            shown: Vec::new(),
        }
    }

    /// Print with [`Printer::trailing`] set to `trailing`, restoring it afterwards.
    fn with_trailing(&mut self, trailing: bool, print: impl FnOnce(&mut Self) -> Doc) -> Doc {
        let saved = std::mem::replace(&mut self.trailing, trailing);
        let printed = print(self);
        self.trailing = saved;
        printed
    }

    /// Enter a binder: its shown name and its type.
    fn bind(&mut self, shown: String, type_: &Expr) {
        self.names.push(shown);
        self.types.push(type_.clone());
        self.shown.push(false);
    }

    /// Leave every binder entered after `depth`.
    fn unbind_to(&mut self, depth: usize) {
        self.names.truncate(depth);
        self.types.truncate(depth);
        self.shown.truncate(depth);
    }

    /// Print current-module private names through their source spelling, as
    /// the pin's default `pp.privateNames = false` delaborator does. All core
    /// lookups and notation decisions retain the original declaration name.
    pub fn in_scope(env: &'a Environment, scope: &'a fln_elab::source::scope::SourceScope) -> Self {
        Self {
            scope: Some(scope),
            resolution: Resolution::read(env),
            pp: PpOptions::read(&scope.options),
            ..Self::new(env)
        }
    }

    /// `∃ x y, b` for `Exists fun x => Exists fun y => b`. The parenthesizer brackets it as
    /// an argument, and where a token follows it (see [`Printer::trailing`]).
    fn exists(&mut self, lambda: &Expr, outer: u32) -> Doc {
        // Under `pp.funBinderTypes` the `fun` carries its binder's type, which only the third
        // pattern matches: `∃ (x : α), b`, never merged with an `∃` inside.
        if self.pp.fun_binder_types
            && let ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                ..
            } = lambda.node()
        {
            let domain = self.with_trailing(false, |printer| printer.doc(binder_type, 0))?;
            let shown = self.bound_name(binder_name, body);
            let depth = self.names.len();
            self.bind(shown.clone(), binder_type);
            let printed = self.with_trailing(false, |printer| printer.doc(body, 0));
            self.unbind_to(depth);
            let binder = node(
                Format::text(format!("({shown} :"))
                    .then(Format::Line)
                    .then(domain)
                    .then(Format::text(")")),
            );
            let shown = Format::text("∃ ")
                .then(binder)
                .then(Format::text(","))
                .then(Format::Line)
                .then(printed?);
            return Ok(if outer >= MAX_PREC || self.trailing {
                node(Format::text("(").then(shown).then(Format::text(")")))
            } else {
                node(shown)
            });
        }
        let depth = self.names.len();
        let mut binders = Vec::new();
        let mut current = lambda.clone();
        let body = loop {
            self.tick()?;
            let ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                ..
            } = current.node()
            else {
                self.unbind_to(depth);
                return Err(Unsupported("an `∃` without its binder"));
            };
            let shown = self.bound_name(binder_name, body);
            self.bind(shown.clone(), binder_type);
            binders.push(shown);
            let (head, args) = spine(body);
            match (head.node(), args.as_slice()) {
                (ExprNode::Const { name, .. }, [_, next])
                    if name.to_display_string() == "Exists"
                        && matches!(
                            next.node(),
                            ExprNode::Lam {
                                binder_info: BinderInfo::Default,
                                ..
                            }
                        ) =>
                {
                    current = next.clone();
                }
                _ => break body.clone(),
            }
        };
        let printed = self.with_trailing(false, |printer| printer.doc(&body, 0));
        self.unbind_to(depth);
        let shown = Format::text(format!("∃ {},", binders.join(" ")))
            .then(Format::Line)
            .then(printed?);
        Ok(if outer >= MAX_PREC || self.trailing {
            node(Format::text("(").then(shown).then(Format::text(")")))
        } else {
            node(shown)
        })
    }

    /// A constant in a term, as the delaborator names it (`pp.fullNames false`), or by its whole
    /// name under `pp.fullNames` (`unresolveNameGlobal` with `fullNames`).
    pub fn display_name(&self, name: &Name) -> String {
        if self.pp.full_names {
            return self.full_name(name);
        }
        match (self.scope, &self.resolution) {
            (Some(scope), Some(resolution)) => {
                escaped_name(&resolution.unresolve(self.env, scope, name))
            }
            _ => self.full_name(name),
        }
    }

    /// `delabConst` (vendored `PrettyPrinter/Delaborator/Builtins.lean:87-128`): the constant's
    /// name, with its universe levels under `pp.universes` (`c.{0, u + 1}`, each level at
    /// precedence 0). A private name under `pp.privateNames` is refused: its internal form is
    /// not reproduced.
    fn constant_head(&self, name: &Name, levels: &[Level]) -> Printed {
        if self.pp.private_names && is_private(name) {
            return Err(Unsupported("a private name under `pp.privateNames`"));
        }
        let shown = self.display_name(name);
        if !self.pp.universes || levels.is_empty() {
            return Ok(shown);
        }
        let levels = levels
            .iter()
            .map(|l| level(l, false))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{shown}.{{{}}}", levels.join(", ")))
    }

    /// A constant by its whole name, as `#check c`'s signature heads it. The pin's
    /// `unresolveNameGlobal` with `fullNames` (vendored `Lean/ResolveName.lean`): a whole
    /// name that resolves to another declaration in this scope is `_root_.`-qualified.
    pub(crate) fn full_name(&self, name: &Name) -> String {
        let Some(scope) = self.scope else {
            return escaped_name(name);
        };
        let shown = scope.user_name(name);
        if let Some(resolution) = &self.resolution
            && !name.has_macro_scopes()
            && matches!(
                scope.resolve_with_aliases(
                    &shown,
                    |declaration| self.env.contains(declaration),
                    &resolution.aliases,
                    &resolution.protected,
                ),
                Ok(Some(found)) if found != *name
            )
        {
            return escaped_name(&Name::from_components(["_root_"]).append_core(&shown));
        }
        escaped_name(&shown)
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

    /// `getParamKinds` for the constant `name` at `levels` applied to `args`: one kind per
    /// leading binder of its type, the default of each binder an argument supplies instantiated
    /// with the universe levels and the arguments before it. Arguments past those binders (an
    /// over-application through a type the pin reduces to a function type) are taken as
    /// regular explicit parameters, as they are for an arrow.
    fn param_kinds(&self, name: &Name, levels: &[Level], args: &[Expr]) -> Vec<ParamKind> {
        let mut kinds = Vec::new();
        if let Some(info) = self.env.find(name) {
            let base = info.constant_val();
            let mut type_ = &base.type_;
            while let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = type_.node()
            {
                let index = kinds.len();
                let default = annotation(binder_type, "optParam").and_then(|(_, value)| {
                    if index >= args.len() {
                        return None;
                    }
                    let value = if base.level_params.len() == levels.len() {
                        fln_elab::universe::parameters::instantiate(
                            || Ok(()),
                            || (),
                            value,
                            &base.level_params,
                            levels,
                        )
                        .ok()?
                    } else {
                        value.clone()
                    };
                    value.subst_loose(0, &args[..index]).ok()
                });
                kinds.push(ParamKind {
                    info: *binder_info,
                    optional: annotation(binder_type, "optParam").is_some(),
                    default,
                    auto: annotation(binder_type, "autoParam").is_some(),
                });
                type_ = body;
            }
        }
        while kinds.len() < args.len() {
            kinds.push(ParamKind {
                info: BinderInfo::Default,
                optional: false,
                default: None,
                auto: false,
            });
        }
        kinds
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
        Self::proof_in(self.env, &self.types, e)
    }

    /// [`Printer::is_proof`] for `e` under the binder types `scope` (innermost last). A `fun`
    /// is a proof when its body is one: its type is a `∀` into the body's type.
    fn proof_in(env: &Environment, scope: &[Expr], e: &Expr) -> bool {
        let mut local: Vec<Expr> = Vec::new();
        let mut e = e;
        loop {
            match e.node() {
                ExprNode::Lam {
                    binder_type, body, ..
                } => {
                    local.push(binder_type.clone());
                    e = body;
                }
                // An ascription's anonymous `let` is its value, the pin's term (`(v : T)`).
                ExprNode::LetE {
                    decl_name,
                    value,
                    body,
                    ..
                } if decl_name.is_anonymous()
                    && matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
                {
                    e = value;
                }
                ExprNode::MData { expr, .. } => e = expr,
                _ => break,
            }
        }
        let (head, args) = spine(e);
        match head.node() {
            ExprNode::Const { name, .. } => env.find(name).is_some_and(|info| {
                let type_ = &info.constant_val().type_;
                if Self::prop_in(env, &[], type_) {
                    return true;
                }
                // A head whose type ends in one of its parameters (`id h`, `sorryAx p b`,
                // `Eq.mpr h p`): the arguments decide, as `inferType` instantiates them.
                let mut result = type_;
                let mut taken = 0;
                while taken < args.len()
                    && let ExprNode::ForallE { body, .. } = result.node()
                {
                    result = body;
                    taken += 1;
                }
                if !matches!(spine(result).0.node(), ExprNode::BVar { .. }) {
                    return false;
                }
                let outside = scope.iter().chain(&local).cloned().collect::<Vec<_>>();
                result
                    .subst_loose(0, &args[..taken])
                    .is_ok_and(|result| Self::prop_in(env, &outside, &result))
            }),
            // A binder's type is relative to the binders outside it.
            ExprNode::BVar { idx } => {
                let idx = usize::try_from(*idx).unwrap_or(usize::MAX);
                if idx < local.len() {
                    let at = local.len() - 1 - idx;
                    let outside = scope
                        .iter()
                        .chain(&local[..at])
                        .cloned()
                        .collect::<Vec<_>>();
                    Self::prop_in(env, &outside, &local[at])
                } else {
                    let outer = idx - local.len();
                    scope
                        .len()
                        .checked_sub(outer + 1)
                        .is_some_and(|at| Self::prop_in(env, &scope[..at], &scope[at]))
                }
            }
            _ => false,
        }
    }

    /// `e` as the pin prints it in a message, broken at the pin's width.
    pub fn expr(&mut self, e: &Expr, outer: u32) -> Printed {
        self.doc(e, outer).map(|doc| doc.pretty(WIDTH))
    }

    /// `indentExpr e` (vendored `src/Lean/Message.lean`): `e` on its own line, nested by two.
    pub(crate) fn indented(&mut self, e: &Expr) -> Printed {
        self.doc(e, 0)
            .map(|doc| Format::Line.then(doc).nest(2).pretty(WIDTH))
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
            if !self.proofs && !atomic(strip_mdata(e)) && self.is_proof(e) {
                return Ok(Format::text("⋯"));
            }
            return self.subterm(e, outer);
        }
        // `pp.beta`: `delabCore` beta-reduces the term first (`Core.betaReduce`).
        let reduced;
        let e = if self.pp.beta {
            reduced = beta_reduce(e)?;
            &reduced
        } else {
            e
        };
        // An ascription's anonymous `let` prints as its value, so the root is that value: the
        // pin's `(e : T)` elaborates to `e` itself, and `e` decides `pp.proofs` there.
        let mut root = e;
        while let ExprNode::LetE {
            decl_name,
            value,
            body,
            ..
        } = root.node()
            && decl_name.is_anonymous()
            && matches!(body.node(), ExprNode::BVar { idx: 0 })
        {
            root = value;
        }
        self.nested = true;
        // `pp.proofs` as set, or, when it is not set, on for a term that is itself a proof.
        // Set off, a proof at the root is omitted like any other (`shouldOmitProof`).
        self.proofs = self.pp.proofs || (!self.pp.proofs_set && self.is_proof(root));
        if !self.proofs && !atomic(strip_mdata(e)) && self.is_proof(e) {
            self.nested = false;
            return Ok(Format::text("⋯"));
        }
        let printed = self.subterm(e, outer);
        self.nested = false;
        // The root is always grouped (`formatCategory` is `fill (nest 2 …)` with no
        // `isUngrouped` check), so a `fun` that is ungrouped as a child is grouped here.
        let lambda = matches!(root.node(), ExprNode::Lam { .. }) && outer == 0;
        printed.map(|doc| if lambda { node(doc) } else { doc })
    }

    fn subterm(&mut self, e: &Expr, outer: u32) -> Doc {
        self.tick()?;
        match e.node() {
            ExprNode::BVar { idx } => {
                let idx = usize::try_from(*idx).unwrap_or(usize::MAX);
                let at = self
                    .names
                    .len()
                    .checked_sub(idx + 1)
                    .ok_or(Unsupported("a loose bound variable"))?;
                if let Some(shown) = self.shown.get_mut(at) {
                    *shown = true;
                }
                self.names
                    .get(at)
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
            // `unexpandUnit` (`Init/NotationExtra.lean:149`).
            ExprNode::Const { name, levels }
                if name.to_display_string() == "Unit.unit"
                    && self.unexpanding(levels)
                    && self.registered("Unit.unit") =>
            {
                Ok(Format::text("()"))
            }
            // A structure's constructor without parameters or fields is a structure instance
            // too, `{ }`.
            ExprNode::Const { name, levels }
                if let Some(ConstantInfo::Ctor(ctor)) = self.env.find(name)
                    && ctor.num_params == 0
                    && ctor.num_fields == 0
                    && self.structure_instances_for(ctor, levels)
                    && let Some(ConstantInfo::Induct(inductive)) = self.env.find(&ctor.induct)
                    && self.structure_like(inductive) =>
            {
                let ctor = ctor.clone();
                self.structure_instance(&ctor, levels, &[])
            }
            ExprNode::Const { name, levels } => {
                if self.unexpanding(levels)
                    && let Some(printed) = self.notation(name, &[], outer)
                {
                    return printed;
                }
                Ok(Format::text(self.constant_at(name, levels)?))
            }
            // `delabLit`: a raw natural literal is `nat_lit n` under `pp.natLit` or `pp.explicit`
            // (`rawNatLit`, a `leading_parser` at `leadPrec`).
            ExprNode::Lit {
                literal: Literal::Nat(value),
            } if self.pp.nat_lit || self.pp.explicit => Ok(paren_doc(
                node(
                    Format::text("nat_lit")
                        .then(Format::Line)
                        .then(Format::text(nat_decimal(value))),
                ),
                MAX_PREC - 1,
                outer,
            )),
            ExprNode::Lit { literal } => Ok(Format::text(match literal {
                Literal::Nat(value) => nat_decimal(value),
                Literal::Str(text) => string_literal(text),
            })),
            ExprNode::MData { expr, .. } => self.doc(expr, outer),
            ExprNode::App { .. } => self.application(e, outer),
            ExprNode::ForallE { .. } => self.pi(e, outer),
            ExprNode::Lam { .. } if self.pp.fun_binder_types => self.typed_lambda(e, outer),
            ExprNode::Lam { .. } => {
                // `fun` is ungrouped (`ppAllowUngrouped`): `fun` ++ ppGroup(binders ++ " =>")
                // ++ line ++ body (vendored `Parser/Term.lean`, `basicFun`).
                let mut binders = Format::Nil;
                let mut body = e;
                let depth = self.names.len();
                // `delabLamAux` (vendored `PrettyPrinter/Delaborator/Builtins.lean:954-1006`)
                // with binder types hidden: an explicit binder is its name, an implicit group
                // `{a b}` and a strict one `⦃a b⦄`. `shouldGroupWithNext` groups a binder
                // with the next when the binder infos agree and the domains are equal as
                // terms. An instance binder shows its type, which is not reproduced.
                let mut group: Vec<String> = Vec::new();
                while let ExprNode::Lam {
                    binder_name: name,
                    binder_type,
                    body: inner,
                    binder_info,
                } = body.node()
                {
                    if *binder_info == BinderInfo::InstImplicit {
                        self.unbind_to(depth);
                        return Err(Unsupported("an instance-implicit `fun` binder"));
                    }
                    if internal_name(name) {
                        self.unbind_to(depth);
                        return Err(INTERNAL_BINDER);
                    }
                    let shown = self.bound_name(name, inner);
                    self.bind(shown.clone(), binder_type);
                    body = inner;
                    if *binder_info == BinderInfo::Default {
                        binders = binders.then(Format::Line).then(Format::text(shown));
                        continue;
                    }
                    group.push(shown);
                    let grouped = matches!(inner.node(), ExprNode::Lam {
                        binder_type: next_type,
                        binder_info: next_info,
                        ..
                    } if next_info == binder_info
                        && binder_type.lift_loose(0, 1).is_ok_and(|lifted| lifted == *next_type));
                    if !grouped {
                        let (open, close) = if *binder_info == BinderInfo::Implicit {
                            ("{", "}")
                        } else {
                            ("⦃", "⦄")
                        };
                        let names = std::mem::take(&mut group).join(" ");
                        binders = binders
                            .then(Format::Line)
                            .then(Format::text(format!("{open}{names}{close}")));
                    }
                }
                let trailing = self.trailing && outer == 0;
                let printed = self.with_trailing(trailing, |printer| printer.doc(body, 0));
                self.unbind_to(depth);
                let fun = Format::text("fun")
                    .then(node(binders.then(Format::text(" =>"))))
                    .then(Format::Line)
                    .then(printed?);
                // `fun` parses at `maxPrec`: the parenthesizer brackets it as an argument and
                // where a token follows it, never merely for an operator's precedence
                // (`id = fun x => x`, `(fun x => x) = id`).
                Ok(if outer >= MAX_PREC || self.trailing {
                    node(Format::text("(").then(fun).then(Format::text(")")))
                } else {
                    fun
                })
            }
            // An anonymous `let : T := v; ·` is how a type ascription `(v : T)` elaborates here;
            // the pin's term is `v` itself. A written `let b := a; b` names its binder.
            ExprNode::LetE {
                decl_name,
                value,
                body,
                ..
            } if decl_name.is_anonymous() && matches!(body.node(), ExprNode::BVar { idx: 0 }) => {
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
                non_dep,
            } if outer == 0 && self.names.len() == self.top_names => {
                if internal_name(name) {
                    return Err(INTERNAL_BINDER);
                }
                let non_dep = &self.nondependent(body, *non_dep)?;
                let declared = self.let_type(type_)?;
                let value = self.doc(value, 0)?;
                let shown = binder_name(name);
                let depth = self.names.len();
                self.bind(shown.clone(), type_);
                // The body continues the chain at the top.
                let top = std::mem::replace(&mut self.top_names, self.names.len());
                let printed = self.doc(body, 0);
                self.top_names = top;
                self.unbind_to(depth);
                Ok(Format::text(format!("{} {shown}", let_keyword(*non_dep)))
                    .then(declared)
                    .then(Format::text(" := "))
                    .then(value)
                    .then(Format::text(";\n"))
                    .then(printed?))
            }
            // Nested, a `let` (`have` when nondependent) is `let x := v;`, the hard line of
            // `optSemicolon`'s `ppLine`, and its body, under `ppDedent`: in parentheses below
            // `leadPrec`, the `paren` node's dedent returns the body to the enclosing
            // indentation, and the hard line breaks every group around it.
            ExprNode::LetE {
                decl_name: name,
                type_,
                value,
                body,
                non_dep,
            } => {
                if internal_name(name) {
                    return Err(INTERNAL_BINDER);
                }
                let non_dep = &self.nondependent(body, *non_dep)?;
                let declared = self.let_type(type_)?;
                let value = self.doc(value, 0)?;
                let shown = binder_name(name);
                let depth = self.names.len();
                self.bind(shown.clone(), type_);
                let printed = self.doc(body, 0);
                self.unbind_to(depth);
                let head = Format::text(format!("{} {shown}", let_keyword(*non_dep)))
                    .then(declared)
                    .then(Format::text(" := "));
                if outer < MAX_PREC {
                    // Unbracketed, the term is its own node, `fill (nest 2 …)`, with the body
                    // under `ppDedent` (`nest (-2)`): its hard line is inside a group, so an
                    // enclosing `fill` breaks before it (`n =⏎  have k := …;⏎  k * k`).
                    return Ok(node(
                        head.then(value)
                            .then(Format::text(";\n").then(printed?).nest(-2)),
                    ));
                }
                let doc = head.then(value).then(Format::text(";\n")).then(printed?);
                Ok(paren_doc(doc, MAX_PREC - 1, outer))
            }
            ExprNode::Proj { idx, expr, .. } => Ok(node(
                self.doc(expr, MAX_PREC)?
                    .then(Format::text(format!(".{}", idx + 1))),
            )),
        }
    }

    /// A `let`'s declared type as `delabLetE` shows it: ` : T` under `pp.letVarTypes`, nothing
    /// otherwise (vendored `PrettyPrinter/Delaborator/Builtins.lean:1080-1097`).
    fn let_type(&mut self, type_: &Expr) -> Doc {
        if !self.pp.let_var_types {
            return Ok(Format::Nil);
        }
        let type_ = self.with_trailing(false, |printer| printer.doc(type_, 0))?;
        Ok(Format::text(" : ").then(type_))
    }

    /// Whether a `let` with this body prints as `have`, under [`Printer::lets`].
    fn nondependent(&self, body: &Expr, non_dep: bool) -> Result<bool, Unsupported> {
        match self.lets {
            _ if non_dep => Ok(true),
            LetMode::AsIs => Ok(false),
            LetMode::ToHave if !body.has_loose_bvar(0) => Ok(true),
            LetMode::ToHave | LetMode::Refuse => Err(Unsupported(
                "a `let` the pin's `letToHave` may make a `have`",
            )),
        }
    }

    /// Whether app unexpanders run on an application headed by a constant at `levels`
    /// (`delabAppImplicitCore`'s `unexpand`, vendored `PrettyPrinter/Delaborator/Builtins.lean:
    /// 364-389`): `pp.notation` is on, the application is in implicit mode (`pp.explicit` is off;
    /// the arity of each notation here leaves no implicit parameter next), and the head has no
    /// universe levels or `pp.universes` is off.
    fn unexpanding(&self, levels: &[Level]) -> bool {
        self.pp.notation && !self.pp.explicit && (levels.is_empty() || !self.pp.universes)
    }

    /// The guards of the builtin delaborators of literals, `delabOfNat`, `delabNeg` and
    /// `delabOfScientific`: `whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions`.
    fn numerals(&self) -> bool {
        !self.pp.explicit && self.pp.coercions
    }

    /// The guards of the builtin notation delaborators (`delabSigma`, `delabSorry`, …):
    /// `whenNotPPOption getPPExplicit <| whenPPOption getPPNotation`.
    fn builtin_notation(&self) -> bool {
        !self.pp.explicit && self.pp.notation
    }

    /// `delabStructureInstance`'s guards on the options (vendored
    /// `PrettyPrinter/Delaborator/Builtins.lean:638-648`): `pp.structureInstances`, a
    /// constructor without universe parameters unless `pp.universes` is off, and none with
    /// parameters under `pp.explicit`.
    fn structure_instances_for(
        &self,
        ctor: &fln_env::constants::ConstructorVal,
        levels: &[Level],
    ) -> bool {
        // A constructor an unexpander prints is never a structure instance; where unexpanders
        // run, [`Printer::structure_instance`] refuses it, and where they do not, it prints as
        // an application.
        if !self.unexpanding(levels)
            && (self.unexpander_in_force(&ctor.base.name) || self.notation_prints(&ctor.base.name))
        {
            return false;
        }
        // In explicit mode, a type printed `⟨…⟩` needs every field explicit.
        let anonymous_explicit = || {
            !self
                .tags
                .as_ref()
                .is_some_and(|tags| tags.anonymous_constructor(&ctor.induct))
                || self
                    .binder_infos(&ctor.base.name)
                    .iter()
                    .skip(ctor.num_params as usize)
                    .all(|info| *info == BinderInfo::Default)
        };
        self.pp.structure_instances
            && (ctor.base.level_params.is_empty() || !self.pp.universes)
            && (!self.pp.explicit || (ctor.num_params == 0 && anonymous_explicit()))
    }

    /// Whether a builtin delaborator this printer does not reproduce prints `function` applied
    /// to `count` arguments under the options in force (vendored
    /// `PrettyPrinter/Delaborator/Builtins.lean:1262-1513`): `dite`'s `if h : c then …`,
    /// `cond`'s `bif`, `⟨a, b⟩` of `PProd.mk`/`MProd.mk`, the ranges, `do`, the lazy binary
    /// operators and name literals. Where one is switched off by `pp.notation` or `pp.explicit`,
    /// the application prints as one.
    fn builtin_unreproduced(&self, function: &str, count: usize) -> bool {
        match function {
            "dite" => self.builtin_notation() && count >= 5,
            "cond" => self.builtin_notation() && count >= 4,
            "PProd.mk" | "MProd.mk" => self.builtin_notation() && count == 4,
            "Bind.bind" => self.builtin_notation() && count == 6,
            "HOrElse.hOrElse" | "HAndThen.hAndThen" | "Seq.seq" | "SeqLeft.seqLeft"
            | "SeqRight.seqRight" => self.builtin_notation() && count >= 6,
            "Std.Rcc.mk" | "Std.Rco.mk" | "Std.Rci.mk" | "Std.Roc.mk" | "Std.Roo.mk"
            | "Std.Roi.mk" | "Std.Ric.mk" | "Std.Rio.mk" | "Std.Rii.mk" => self.builtin_notation(),
            "Std.Legacy.Range.mk" => self.pp.notation && count == 4,
            "Lean.Name.str" | "Lean.Name.num" | "Lean.Name.mkStr1" | "Lean.Name.mkStr2"
            | "Lean.Name.mkStr3" | "Lean.Name.mkStr4" | "Lean.Name.mkStr5" | "Lean.Name.mkStr6"
            | "Lean.Name.mkStr7" | "Lean.Name.mkStr8" => self.pp.notation,
            // `delabAppMatch`: a matcher application is `match … with`, under `pp.match` too.
            _ => {
                self.builtin_notation()
                    && self.pp.match_
                    && function.rsplit('.').next().is_some_and(|leaf| {
                        leaf.strip_prefix("match_")
                            .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
                    })
            }
        }
    }

    /// The numeric literals of `delabOfNat`, `delabNeg` and `delabHDiv` (vendored
    /// `PrettyPrinter/Delaborator/Builtins.lean:1112-1187`): `n` for `OfNat.ofNat T n _`, `-n`
    /// for its negation, and `p / q` for a homogeneous division of one by a numeral. Under
    /// `pp.numericTypes` each is ascribed its type, `(n : T)`. `None` where none applies.
    fn numeric_literal(&mut self, function: &str, args: &[Expr], outer: u32) -> Option<Doc> {
        let numeral = |e: &Expr| {
            let (head, args) = spine(e);
            match (head.node(), args.as_slice()) {
                (ExprNode::Const { name, .. }, [_, value, _])
                    if name.to_display_string() == "OfNat.ofNat" =>
                {
                    match value.node() {
                        ExprNode::Lit {
                            literal: Literal::Nat(value),
                        } => Some(nat_decimal(value)),
                        _ => None,
                    }
                }
                _ => None,
            }
        };
        let negative = |e: &Expr| {
            let (head, args) = spine(e);
            match (head.node(), args.as_slice()) {
                (ExprNode::Const { name, .. }, [_, _, operand])
                    if name.to_display_string() == "Neg.neg" =>
                {
                    numeral(operand).map(|n| format!("-{n}"))
                }
                _ => None,
            }
        };
        let (literal, precedence) = match (function, args) {
            ("OfNat.ofNat", [_, value, _]) => match value.node() {
                ExprNode::Lit {
                    literal: Literal::Nat(value),
                } => (nat_decimal(value), MAX_PREC),
                _ => return None,
            },
            ("Neg.neg", [_, _, operand]) => (format!("-{}", numeral(operand)?), 75),
            ("HDiv.hDiv", [a, b, c, _, p, q]) if a == b && b == c => {
                let p = numeral(p).or_else(|| negative(p))?;
                (format!("{p} / {}", numeral(q)?), 70)
            }
            _ => return None,
        };
        if !self.pp.numeric_types {
            // `-n` and `p / q` are notation nodes, laid out as their unexpanders lay them out.
            let doc = match literal.split_once(" / ") {
                Some((p, q)) => node(
                    Format::text(format!("{p} /"))
                        .then(Format::Line)
                        .then(Format::text(q)),
                ),
                None if precedence == 75 => node(Format::text(literal)),
                None => Format::text(literal),
            };
            return Some(Ok(paren_doc(doc, precedence, outer)));
        }
        let shown = match literal.split_once(" / ") {
            Some((p, q)) => node(
                Format::text(format!("{p} /"))
                    .then(Format::Line)
                    .then(Format::text(q)),
            ),
            None => Format::text(literal),
        };
        Some(self.ascribed(shown, &args[0]))
    }

    fn application(&mut self, e: &Expr, outer: u32) -> Doc {
        let (head, args) = spine(e);
        if let ExprNode::Const { name, levels } = head.node() {
            let text = name.to_display_string();
            let unexpanding = self.unexpanding(levels);
            // `delabChar` (vendored `PrettyPrinter/Delaborator/Builtins.lean:1099-1104`), under
            // every option: `Char.ofNat` of a literal is the character literal.
            if text == "Char.ofNat"
                && let [arg] = args.as_slice()
                && let ExprNode::Lit {
                    literal: Literal::Nat(value),
                } = arg.node()
            {
                return value
                    .to_u64()
                    .and_then(|code| u32::try_from(code).ok())
                    .and_then(char::from_u32)
                    .map(|c| Format::text(char_literal(c)))
                    .ok_or(Unsupported(
                        "a character literal that is not a scalar value",
                    ));
            }
            if self.builtin_unreproduced(&text, args.len()) {
                return Err(Unsupported(
                    "an application a builtin notation delaborator prints",
                ));
            }
            if self.numerals()
                && let Some(printed) = self.numeric_literal(&text, &args, outer)
            {
                return printed;
            }
            // The source's own notations: their unexpanders are the newest.
            if unexpanding && let Some(printed) = self.notation(name, &args, outer) {
                return printed;
            }
            // `notation:max "¬" p:40 => Not p`; `notation:max "!" b:40 => not b`
            // (`Init/Notation.lean`, `not` being `Bool.not`).
            if (text == "Not" || text == "Bool.not") && args.len() == 1 && unexpanding {
                let symbol = if text == "Not" { "¬" } else { "!" };
                return Ok(paren_doc(
                    node(Format::text(symbol).then(self.doc(&args[0], 40)?)),
                    MAX_PREC,
                    outer,
                ));
            }
            // `delabSigma`/`delabPSigma` (vendored `PrettyPrinter/Delaborator/Builtins.lean:
            // 1300-1317`): `Sigma fun (x : α) => b` is `(x : α) × b`, `(_ : α) × b` when `b` does
            // not use `x`. The notation (`macro:35 … " × " b:term:35`) is declared in
            // `Init.NotationExtra`; without it the pin fails to print the term at all.
            if (text == "Sigma" || text == "PSigma")
                && args.len() == 2
                && self.builtin_notation()
                && let ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    ..
                } = args[1].node()
            {
                if !self.registered(&text) {
                    return Err(Unsupported("a `Σ` type without `Init.NotationExtra`"));
                }
                let domain = self.with_trailing(false, |printer| printer.doc(binder_type, 0))?;
                let shown = if body.has_loose_bvar(0) {
                    self.bound_name(binder_name, body)
                } else {
                    "_".to_owned()
                };
                let depth = self.names.len();
                self.bind(shown.clone(), binder_type);
                let trailing = self.trailing && 35 >= outer;
                let printed = self.with_trailing(trailing, |printer| printer.doc(body, 35));
                self.unbind_to(depth);
                let symbol = if text == "Sigma" { " ×" } else { " ×'" };
                let doc = Format::text(format!("({shown} : "))
                    .then(domain)
                    .then(Format::text(")"))
                    .then(Format::text(symbol))
                    .then(Format::Line)
                    .then(printed?);
                return Ok(paren_doc(node(doc), 35, outer));
            }
            // `unexpandSubtype` (`Init/NotationExtra.lean:199-202`): `Subtype fun x => p` is
            // `{ x // p }`, and `{ x : α // p }` under `pp.funBinderTypes`, the `fun` carrying its
            // binder's type (`"{ " ident (" : " term)? " // " term " }"`, `Init/Notation.lean:577`).
            if text == "Subtype"
                && args.len() == 2
                && unexpanding
                && self.registered("Subtype")
                && let ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info: BinderInfo::Default,
                } = args[1].node()
            {
                if internal_name(binder_name) {
                    return Err(INTERNAL_BINDER);
                }
                let domain = if self.pp.fun_binder_types {
                    Some(self.with_trailing(false, |printer| printer.doc(binder_type, 0))?)
                } else {
                    None
                };
                let shown = self.bound_name(binder_name, body);
                let depth = self.names.len();
                self.bind(shown.clone(), binder_type);
                let printed = self.with_trailing(false, |printer| printer.doc(body, 0));
                self.unbind_to(depth);
                let mut doc = Format::text("{")
                    .then(Format::Line)
                    .then(Format::text(shown));
                if let Some(domain) = domain {
                    doc = doc.then(Format::text(" :")).then(Format::Line).then(domain);
                }
                return Ok(node(
                    doc.then(Format::text(" //"))
                        .then(Format::Line)
                        .then(printed?)
                        .then(Format::text(" }")),
                ));
            }
            // `unexpandExists` (`Init/NotationExtra.lean:185-189`): `Exists fun x => b` is
            // `∃ x, b`, nested ones sharing one binder list. A `fun` binder that is not
            // explicit does not match the unexpander and is not reproduced.
            if text == "Exists"
                && args.len() == 2
                && unexpanding
                && self.registered("Exists")
                && matches!(
                    args[1].node(),
                    ExprNode::Lam {
                        binder_info: BinderInfo::Default,
                        ..
                    }
                )
            {
                return self.exists(&args[1], outer);
            }
            // `prefix:75 "-" => Neg.neg` (`Init/Notation.lean:293`), and `delabNeg`'s negative
            // numeral (vendored `PrettyPrinter/Delaborator/Builtins.lean:1171-1177`), which
            // prints the same and is not an unexpander.
            if text == "Neg.neg"
                && args.len() == 3
                && (unexpanding || (self.numerals() && ofnat_literal(&args[2])))
            {
                let trailing = self.trailing && 75 >= outer;
                let operand = self.with_trailing(trailing, |printer| printer.doc(&args[2], 75))?;
                // `--` would begin a comment: the pin separates the tokens, not reproduced.
                if flat(&operand).starts_with('-') {
                    return Err(Unsupported("a negated negation"));
                }
                return Ok(paren_doc(node(Format::text("-").then(operand)), 75, outer));
            }
            // `delabOfScientific` (vendored `PrettyPrinter/Delaborator/Builtins.lean:1190-1207`).
            if text == "OfScientific.ofScientific"
                && args.len() == 5
                && self.numerals()
                && let ExprNode::Lit {
                    literal: Literal::Nat(mantissa),
                } = args[2].node()
                && let ExprNode::Lit {
                    literal: Literal::Nat(exponent),
                } = args[4].node()
                && let ExprNode::Const { name: sign, .. } = args[3].node()
                && let Some(negative) = match sign.to_display_string().as_str() {
                    "Bool.true" => Some(true),
                    "Bool.false" => Some(false),
                    _ => None,
                }
            {
                return Ok(Format::text(scientific(
                    &nat_decimal(mantissa),
                    negative,
                    &nat_decimal(exponent),
                )));
            }
            // `[a, b, …]` (the `List.cons`/`List.nil` unexpanders); an open tail is `::`.
            if text == "List.cons"
                && args.len() == 3
                && unexpanding
                && self.registered("List.cons")
                && self.registered("List.nil")
            {
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
            if text == "List.nil" && args.len() == 1 && unexpanding && self.registered("List.nil") {
                return Ok(Format::text("[]"));
            }
            // Each operator is an `infixl`/`infixr`/`notation` of `Init.Notation`, which registers
            // its unexpander: without that import the pin prints the application.
            if let Some(infix) = INFIXES
                .iter()
                .find(|infix| infix.function == text && infix.arity == args.len())
                .filter(|infix| unexpanding && self.registered(infix.function))
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
                let lhs = self
                    .with_trailing(true, |printer| printer.doc(&args[args.len() - 2], lhs_prec))?;
                // A right operand that is a bare `fun` would absorb a token after the
                // operation: the parenthesizer brackets the operation whole there,
                // `(id = fun x => x) ∧ True`, as it does an application ending so. A `fun`
                // operand that nothing follows is left bare, as an application's last argument
                // is (`argument`): the pin prints `(fun x => x) = fun x => x`.
                let bare_fun = matches!(
                    strip_mdata(&args[args.len() - 1]).node(),
                    ExprNode::Lam { .. }
                );
                let open = self.trailing && infix.precedence >= outer && bare_fun;
                let trailing = self.trailing && infix.precedence >= outer && !open;
                let rhs = if !trailing && bare_fun {
                    self.with_trailing(false, |printer| printer.doc(&args[args.len() - 1], 0))?
                } else {
                    self.with_trailing(trailing, |printer| {
                        printer.doc(&args[args.len() - 1], rhs_prec)
                    })?
                };
                let doc = node(
                    lhs.then(Format::text(format!(" {}", infix.symbol)))
                        .then(Format::Line)
                        .then(rhs),
                );
                return Ok(if open {
                    paren_doc(doc, 0, 1)
                } else {
                    paren_doc(doc, infix.precedence, outer)
                });
            }
            // `coeDelaborator` (vendored `PrettyPrinter/Delaborator/Builtins.lean:1230-1260`): a
            // function the `coe` attribute registers is `↑x` of its first explicit argument
            // when applied to exactly that many arguments. The pinned `Init` registers four:
            // `Nat.cast` (`Init/Data/Cast.lean:69`), `Int.cast` (`Init/Data/Int/Basic.lean:453`),
            // `Fin.val` (`Init/Prelude.lean:2321`), `Subarray.copy`
            // (`Init/Data/Slice/Array/Iterator.lean:88`).
            if matches!(
                text.as_str(),
                "Nat.cast" | "Int.cast" | "Fin.val" | "Subarray.copy"
            ) && let Some(coercee) = self
                .binder_infos(name)
                .iter()
                .position(|info| *info == BinderInfo::Default)
                // `whenPPOption getPPCoercions`; under `pp.explicit` a coercion whose coercee is not
                // its first argument is not one (each of the four's is not).
                && self.pp.coercions
                && !(self.pp.explicit && coercee != 0)
            {
                if args.len() == coercee + 1 {
                    let shown = self.doc(&args[coercee], MAX_PREC)?;
                    let coercion = node(Format::text("↑").then(shown));
                    // `withTypeAscription (cond := ← getPPOption getPPCoercionsTypes)`.
                    if self.pp.coercions_types {
                        let type_ = self.application_type(name, levels, &args)?;
                        return self.ascribed(coercion, &type_);
                    }
                    return Ok(coercion);
                }
                if args.len() > coercee + 1 {
                    return Err(Unsupported("an applied coercion"));
                }
            }
            // `delabSorry` (vendored `PrettyPrinter/Delaborator/Builtins.lean:1515-1542`): a
            // labeled sorry, `sorryAx (Lean.Name → α) synthetic tag`, and a plain one,
            // `sorryAx α synthetic`, both print `sorry`; arguments beyond are applied after it.
            if text == "sorryAx" && args.len() >= 2 && self.builtin_notation() {
                let labeled = matches!(args[0].node(), ExprNode::ForallE { binder_type, .. }
                    if matches!(binder_type.node(), ExprNode::Const { name, .. }
                        if name.to_display_string() == "Lean.Name"));
                let consumed = if labeled { 3 } else { 2 };
                if args.len() == consumed {
                    return Ok(Format::text("sorry"));
                }
                return Err(Unsupported("an applied sorry"));
            }
            if text == "Prod.mk" && args.len() == 4 && unexpanding && self.registered("Prod.mk") {
                return self.tuple(&args[2], &args[3]);
            }
            // A structure's constructor, fully applied, is `{ x := a, … }` at the pin, or
            // `⟨a, …⟩` for a type tagged `pp_using_anonymous_constructor` ([`structures`]).
            if let Some(ConstantInfo::Ctor(ctor)) = self.env.find(name)
                && args.len() == (ctor.num_params + ctor.num_fields) as usize
                && self.structure_instances_for(ctor, levels)
                && let Some(ConstantInfo::Induct(inductive)) = self.env.find(&ctor.induct)
                && self.structure_like(inductive)
            {
                let ctor = ctor.clone();
                return self.structure_instance(&ctor, levels, &args);
            }
            // Any other constant an imported `@[app_unexpander]` prints (`ite` as `if … then …
            // else …`, `GetElem.getElem` as `xs[i]`, …) runs code this door does not reproduce:
            // its application is refused rather than printed as an application. Where no
            // unexpander runs, the application prints as one.
            if unexpanding && self.imported_tags && self.unexpander_in_force(name) {
                return Err(Unsupported("an application an `@[app_unexpander]` prints"));
            }
            let kinds = self.param_kinds(name, levels, &args);
            // `delabAppExplicitCore`: every argument, implicit and instance ones included, after
            // `@c` (`needsExplicit`). The pin takes explicit mode under `pp.explicit`, and
            // otherwise when the next parameter is implicit (`@List.map Nat`) or a later explicit
            // one has a default (`@f 1`).
            if self.pp.explicit || app_explicit(args.len(), &kinds) {
                return self.explicit_application(name, levels, &args, &kinds, outer);
            }
            let infos = self.binder_infos(name);
            // `delabAppImplicitCore`'s field notation: `pp.fieldNotation`, and a head without
            // universe levels or `pp.universes` off.
            let receiver = if self.pp.field_notation && (levels.is_empty() || !self.pp.universes) {
                self.field_receiver(name, &infos, &args)
            } else {
                None
            };
            // `delabAppImplicitCore`'s `mkArg`: an argument equal to its parameter's default is
            // optional, then the field-notation object and explicit arguments are shown; the
            // trailing optional arguments are dropped (`f 1` for `f 1 3`, `f n m := 3`).
            let mut kinds_shown: Vec<Shown> = args
                .iter()
                .zip(&kinds)
                .enumerate()
                .map(|(index, (arg, kind))| {
                    if kind.default.as_ref() == Some(arg) {
                        Shown::Optional
                    } else if receiver.as_ref().is_some_and(|(at, _)| *at == index)
                        || kind.info == BinderInfo::Default
                    {
                        Shown::Regular
                    } else {
                        Shown::Skip
                    }
                })
                .collect();
            while kinds_shown.last() == Some(&Shown::Optional) {
                kinds_shown.pop();
            }
            let shown_args: Vec<usize> = (0..kinds_shown.len())
                .filter(|&index| kinds_shown[index] != Shown::Skip)
                .collect();
            // Generalized field notation: `C.f r …` is `r.f …` when `r` is `C.f`'s first
            // explicit argument and has type `C …` (never on a numeric literal). The object
            // must remain a regular argument once the optional ones are dropped.
            if let Some((receiver, field)) = receiver
                && kinds_shown.get(receiver) == Some(&Shown::Regular)
            {
                let object = self.without_parent_projections(&args[receiver], false)?;
                let projection = node(
                    self.doc(&object, MAX_PREC)?
                        .then(Format::text(format!(".{field}"))),
                );
                let mut shown = projection;
                let mut applied = false;
                let shown_args: Vec<usize> = shown_args
                    .into_iter()
                    .filter(|&index| index != receiver)
                    .collect();
                let mut open = false;
                for (position, &index) in shown_args.iter().enumerate() {
                    let last = position + 1 == shown_args.len();
                    let (printed, bare) = self.argument(&args[index], last)?;
                    shown = shown.then(Format::Line).then(printed);
                    open = bare;
                    applied = true;
                }
                return Ok(if applied {
                    self.applied(node(shown), open, outer)
                } else {
                    shown
                });
            }
            let mut shown = Format::Nil;
            let mut applied = false;
            let mut open = false;
            for (position, &index) in shown_args.iter().enumerate() {
                let last = position + 1 == shown_args.len();
                let (printed, bare) = self.argument(&args[index], last)?;
                shown = shown.then(Format::Line).then(printed);
                open = bare;
                applied = true;
            }
            let text = self.constant_head(name, levels)?;
            if !applied {
                return Ok(Format::text(text));
            }
            // `app := many1 argument`, each argument after a line (`checkWsBefore`).
            return Ok(self.applied(node(Format::text(text).then(shown)), open, outer));
        }
        // A bound variable applied: every argument is shown, which is the pin's printing only
        // when each parameter it supplies is explicit and the next is neither implicit nor an
        // instance (`getParamKinds` of the variable's type, `needsExplicit`).
        if let ExprNode::BVar { .. } = head.node()
            && let Ok(type_) = self.infer_type(&head)
        {
            let mut type_ = &type_;
            for _ in 0..args.len() {
                match type_.node() {
                    ExprNode::ForallE {
                        body,
                        binder_info: BinderInfo::Default,
                        binder_type,
                        ..
                    } if annotation(binder_type, "optParam").is_none()
                        && annotation(binder_type, "autoParam").is_none() =>
                    {
                        type_ = body;
                    }
                    ExprNode::ForallE { .. } => {
                        return Err(Unsupported(
                            "a bound variable applied to an implicit or defaulted argument",
                        ));
                    }
                    _ => break,
                }
            }
            if let ExprNode::ForallE { binder_info, .. } = type_.node()
                && *binder_info != BinderInfo::Default
                && *binder_info != BinderInfo::StrictImplicit
            {
                return Err(Unsupported(
                    "a bound variable applied before an implicit parameter",
                ));
            }
        }
        let mut shown = self.doc(&head, MAX_PREC)?;
        let mut open = false;
        for (index, arg) in args.iter().enumerate() {
            let last = index + 1 == args.len();
            let (printed, bare) = self.argument(arg, last)?;
            shown = shown.then(Format::Line).then(printed);
            open = bare;
        }
        Ok(self.applied(node(shown), open, outer))
    }

    /// Whether an `@[app_unexpander]` is registered for `key`, which this printer reproduces.
    fn registered(&self, key: &str) -> bool {
        match &self.tags {
            Some(_) if self.imported_tags => {
                self.unexpander_in_force(&Name::from_components(key.split('.')))
            }
            _ => true,
        }
    }

    /// Whether an imported `@[app_unexpander]` for `constant` is in force here. A `scoped` one
    /// is in force where its namespace is active in this command's scope. Without a scope,
    /// every registered one is taken to be in force.
    fn unexpander_in_force(&self, constant: &Name) -> bool {
        self.tags.as_ref().is_some_and(|tags| {
            tags.unexpanded(constant, |namespace| {
                self.scope
                    .is_none_or(|scope| scope.instance_scopes.is_active(namespace))
            })
        })
    }

    /// `unexpandProdMk` (`Init/NotationExtra.lean:168-171`): `Prod.mk x y` is `(x, y)`, and a
    /// second component that is itself a pair continues the tuple, `(x, y, z)`.
    fn tuple(&mut self, first: &Expr, second: &Expr) -> Doc {
        let mut elements = vec![first.clone()];
        let mut rest = second.clone();
        loop {
            self.tick()?;
            let (head, args) = spine(&rest);
            match head.node() {
                ExprNode::Const { name, .. }
                    if name.to_display_string() == "Prod.mk" && args.len() == 4 =>
                {
                    elements.push(args[2].clone());
                    rest = args[3].clone();
                }
                _ => break,
            }
        }
        elements.push(rest);
        // `"(" term ", " sepBy1 term ", " ")"`: a line after each comma.
        let mut shown = Format::Nil;
        for (index, element) in elements.iter().enumerate() {
            if index > 0 {
                shown = shown.then(Format::text(",")).then(Format::Line);
            }
            shown = shown.then(self.with_trailing(false, |printer| printer.doc(element, 0))?);
        }
        Ok(node(Format::text("(").then(shown).then(Format::text(")"))))
    }

    /// An application's argument, at `maxPrec`, and whether it is a `fun` left bare. `fun`
    /// parses at `maxPrec` too (`basicFun`), so the pin's parenthesizer brackets it only before a
    /// later argument: last, it is `Subtype fun n => n = 1`, and an application ending so is
    /// bracketed whole where a token follows it ([`Printer::applied`]).
    fn argument(&mut self, arg: &Expr, last: bool) -> Result<(Format, bool), Unsupported> {
        let mut bare = arg;
        while let ExprNode::MData { expr, .. } = bare.node() {
            bare = expr;
        }
        if last && matches!(bare.node(), ExprNode::Lam { .. }) {
            Ok((
                self.with_trailing(false, |printer| printer.doc(arg, 0))?,
                true,
            ))
        } else {
            Ok((self.doc(arg, MAX_PREC)?, false))
        }
    }

    /// `paren_doc` for an application at `outer`, also bracketed when it ends in a bare `fun`
    /// and a token follows it: `(ap2 1 fun x => x) + 2`, `(Subtype fun n => n = 1) → Nat`.
    fn applied(&self, doc: Format, open: bool, outer: u32) -> Format {
        if open && self.trailing && outer < MAX_PREC {
            paren_doc(doc, 0, 1)
        } else {
            paren_doc(doc, MAX_PREC - 1, outer)
        }
    }

    /// `delabAppExplicitCore` (vendored `PrettyPrinter/Delaborator/Builtins.lean:290-332`): the
    /// head, with `@` when `needsExplicit`, and every argument. Without `@`, the application may
    /// use field notation (`pp.fieldNotation`, not under `pp.tagAppFns`, and a head without
    /// universe levels unless `pp.universes` is off). An instance argument is `_` without
    /// `pp.instances`, and ascribed its type under `pp.instanceTypes`.
    fn explicit_application(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
        kinds: &[ParamKind],
        outer: u32,
    ) -> Doc {
        let insert = needs_explicit(args.len(), kinds);
        let receiver = if !insert
            && self.pp.field_notation
            && !self.pp.tag_app_fns
            && (levels.is_empty() || !self.pp.universes)
        {
            let infos = self.binder_infos(name);
            self.field_receiver(name, &infos, args)
        } else {
            None
        };
        let mut printed = Vec::with_capacity(args.len());
        for (index, arg) in args.iter().enumerate() {
            let last = index + 1 == args.len();
            if receiver.as_ref().is_some_and(|(at, _)| *at == index) {
                let object = self.without_parent_projections(arg, true)?;
                printed.push((self.doc(&object, MAX_PREC)?, false));
                continue;
            }
            if kinds
                .get(index)
                .is_some_and(|kind| kind.info == BinderInfo::InstImplicit)
            {
                if self.pp.instance_types {
                    let shown = if self.pp.instances {
                        self.with_trailing(false, |printer| printer.doc(arg, 0))?
                    } else {
                        Format::text("_")
                    };
                    let type_ = self.infer_type(arg)?;
                    printed.push((self.ascribed(shown, &type_)?, false));
                } else if self.pp.instances {
                    printed.push(self.argument(arg, last)?);
                } else {
                    printed.push((Format::text("_"), false));
                }
                continue;
            }
            printed.push(self.argument(arg, last)?);
        }
        if let Some((at, field)) = receiver {
            let (object, _) = printed.remove(at);
            let mut shown = node(object.then(Format::text(format!(".{field}"))));
            if printed.is_empty() {
                return Ok(shown);
            }
            let mut open = false;
            for (doc, bare) in printed {
                shown = shown.then(Format::Line).then(doc);
                open = bare;
            }
            return Ok(self.applied(node(shown), open, outer));
        }
        let head = self.constant_head(name, levels)?;
        let mut shown = Format::text(if insert { format!("@{head}") } else { head });
        if printed.is_empty() {
            return Ok(shown);
        }
        let mut open = false;
        for (doc, bare) in printed {
            shown = shown.then(Format::Line).then(doc);
            open = bare;
        }
        Ok(self.applied(node(shown), open, outer))
    }

    /// `withTypeAscription` (vendored `PrettyPrinter/Delaborator/Builtins.lean:28-36`):
    /// `(e : T)`, the `typeAscription` node, its `" :"` token followed by `ppSpace`.
    fn ascribed(&mut self, doc: Format, type_: &Expr) -> Doc {
        let type_ = self.with_trailing(false, |printer| printer.doc(type_, 0))?;
        Ok(node(
            Format::text("(")
                .then(doc)
                .then(Format::text(" :"))
                .then(Format::Line)
                .then(type_)
                .then(Format::text(")")),
        ))
    }

    /// The type of `e` where it is read off without reduction: a bound variable's, or a
    /// constant's applied to arguments that its type's leading binders take (`inferType`).
    fn infer_type(&self, e: &Expr) -> Result<Expr, Unsupported> {
        let unknown = Unsupported("the type of a term this printer does not infer");
        let (head, args) = spine(strip_mdata(e));
        match head.node() {
            ExprNode::Const { name, levels } => self.application_type(name, levels, &args),
            ExprNode::BVar { idx } if args.is_empty() => {
                let index = usize::try_from(*idx).map_err(|_| unknown.clone())?;
                let at = self
                    .types
                    .len()
                    .checked_sub(index + 1)
                    .ok_or(unknown.clone())?;
                self.types[at].lift_loose(0, *idx + 1).map_err(|_| unknown)
            }
            _ => Err(unknown),
        }
    }

    /// The type of `name` at `levels` applied to `args`: its type with the universe parameters
    /// instantiated and one leading binder taken per argument. A type that would have to be
    /// reduced to a function type first is refused.
    fn application_type(
        &self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Expr, Unsupported> {
        let unknown = Unsupported("the type of an application this printer does not infer");
        let info = self.env.find(name).ok_or(unknown.clone())?;
        let base = info.constant_val();
        if base.level_params.len() != levels.len() {
            return Err(unknown);
        }
        let mut type_ = fln_elab::universe::parameters::instantiate(
            || Ok(()),
            || (),
            &base.type_,
            &base.level_params,
            levels,
        )
        .map_err(|_| unknown.clone())?;
        for _ in args {
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Err(unknown);
            };
            type_ = body.clone();
        }
        type_.subst_loose(0, args).map_err(|_| unknown)
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
        // `fieldNotationCandidate?` / `generalizedFieldInfo` (vendored
        // `PrettyPrinter/Delaborator/FieldNotation.lean:76-137`): never in `Function`, never on
        // a theorem, never on `pp_nodot` (in `Init` only `List.toArrayImpl`,
        // `Init/Data/List/ToArrayImpl.lean:35`).
        if namespace.is_anonymous()
            || namespace.to_display_string() == "Function"
            || name.to_display_string() == "List.toArrayImpl"
            || self.tags.as_ref().is_some_and(|tags| tags.nodot(name))
        {
            return None;
        }
        let signature = &self.env.find(name)?.constant_val().type_;
        if Self::prop_in(self.env, &[], signature) {
            return None;
        }
        // The first parameter whose type is an application of the namespace is the receiver;
        // it must be explicit, and no explicit parameter may come before it. A `motive` before
        // it stops field notation.
        let mut type_ = signature;
        let mut receiver = None;
        for index in 0..args.len() {
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } = type_.node()
            else {
                return None;
            };
            if binder_name.to_display_string() == "motive" {
                return None;
            }
            let explicit = infos.get(index) == Some(&BinderInfo::Default);
            // `isAppOfBaseName` reads the type after `cleanupAnnotations` (`@& Nat` is `Nat`).
            let mut domain = binder_type;
            while let ExprNode::MData { expr, .. } = domain.node() {
                domain = expr;
            }
            if matches!(spine(domain).0.node(),
                ExprNode::Const { name: head, .. } if *head == namespace)
            {
                if !explicit {
                    return None;
                }
                receiver = Some(index);
                break;
            }
            if explicit {
                return None;
            }
            type_ = body;
        }
        let receiver = receiver?;
        let arg = args.get(receiver)?;
        let literal = matches!(arg.node(), ExprNode::Lit { .. })
            || matches!(spine(arg).0.node(),
                ExprNode::Const { name, .. } if name.to_display_string() == "OfNat.ofNat");
        if literal {
            return None;
        }
        Some((receiver, escaped_part(field, false)))
    }

    /// A bare constant, as the pin's application delaborator prints it with no arguments: `@c`
    /// in explicit mode (`useAppExplicit`, `needsExplicit`), which a first parameter that is
    /// implicit or an instance selects, and so does an explicit parameter with a default or a
    /// tactic (`@f : Nat → optParam Nat 3 → Nat`). A strict implicit first parameter does not.
    pub fn constant(&self, name: &Name) -> String {
        let kinds = self.param_kinds(name, &[], &[]);
        if app_explicit(0, &kinds) && needs_explicit(0, &kinds) {
            format!("@{}", self.display_name(name))
        } else {
            self.display_name(name)
        }
    }

    /// [`Printer::constant`] at `levels`, under the options in force ([`Printer::constant_head`]).
    fn constant_at(&self, name: &Name, levels: &[Level]) -> Printed {
        let kinds = self.param_kinds(name, levels, &[]);
        let head = self.constant_head(name, levels)?;
        Ok(if needs_explicit(0, &kinds) {
            format!("@{head}")
        } else {
            head
        })
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
        default: Option<Format>,
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
        let mut doc = doc.then(Format::text(" :")).then(Format::Line).then(type_);
        // `binderDefault` (`" := " term`, vendored `Parser/Term/Basic.lean`).
        if let Some(default) = default {
            doc = doc
                .then(Format::text(" :="))
                .then(Format::Line)
                .then(default);
        }
        node(doc.then(Format::text(close)))
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
        // On a signature's spine after its colon, an accessible binder name not already in
        // scope is shown as if the binder were dependent (`delabForallBinders`' `dep` with
        // `pp.piBinderNames`); one already in scope was renamed inaccessible by `processSpine`.
        let spine = std::mem::take(&mut self.spine_names);
        // Under `pp.piBinderNames` every binder name without macro scopes shows (with
        // `pp.piBinderNames.hygienic`, every one), as if the binder were dependent.
        let named = |printer: &Self, name: &Name| {
            (spine && accessible(name) && !printer.names.contains(&escaped_name(name)))
                || (printer.pp.pi_binder_names
                    && (!name.has_macro_scopes() || printer.pp.pi_binder_names_hygienic))
        };
        // `∀` notation, and the binder names RFC #1834 shows, are for propositions under
        // `pp.foralls`; without it a proposition prints with arrows.
        let proposition = self.pp.foralls && self.is_prop(e);
        // `delabForallBinders` (vendored `PrettyPrinter/Delaborator/Builtins.lean:1020-1031`): a
        // binder shows its name when it is dependent, and also (RFC #1834, `pp.foralls`) when
        // it is explicit, in a proposition, and its domain is not a proposition.
        let dependent = body.has_loose_bvar(0)
            || named(self, name)
            || (proposition && *binder_info == BinderInfo::Default && !self.is_prop(binder_type));
        // A non-dependent explicit binder is an arrow (or an implication): `arrow` is
        // `term " → " term`, the token's trailing space a line.
        if !dependent && *binder_info == BinderInfo::Default {
            let domain =
                self.with_trailing(true, |printer| printer.doc(binder_type, ARROW_PREC + 1))?;
            let shown = self.bound_name(name, body);
            let depth = self.names.len();
            self.bind(shown, binder_type);
            let trailing = self.trailing && ARROW_PREC >= outer;
            self.spine_names = spine && matches!(body.node(), ExprNode::ForallE { .. });
            let codomain = self.with_trailing(trailing, |printer| printer.doc(body, ARROW_PREC));
            self.spine_names = false;
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
            let dependent = body.has_loose_bvar(0)
                || named(self, name)
                || (proposition
                    && *binder_info == BinderInfo::Default
                    && !self.is_prop(binder_type));
            if !dependent && *binder_info == BinderInfo::Default {
                self.spine_names = spine;
                let printed = self.pi(current, ARROW_PREC);
                self.spine_names = false;
                break printed;
            }
            if internal_name(name) {
                break Err(INTERNAL_BINDER);
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
                let other_dependent = other_body.has_loose_bvar(0)
                    || named(self, other)
                    || (proposition
                        && *other_info == BinderInfo::Default
                        && !self.is_prop(other_type));
                if other_info != binder_info || !other_dependent {
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
            groups.push(self.binder_group(*binder_info, &names, type_doc, hidden, None));
            current = next;
            if proposition {
                // `∀ (x : A) (y : B), p` keeps collecting dependent binders.
                continue;
            }
            // `(x : A) → B`: `depArrow` is `bracketedBinder " → " term`.
            self.spine_names = spine && matches!(current.node(), ExprNode::ForallE { .. });
            let rest = self.pi_tail(current);
            self.spine_names = false;
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

    /// `fun` under `pp.funBinderTypes` (`delabLamAux`, vendored
    /// `PrettyPrinter/Delaborator/Builtins.lean:954-1010`): every binder group shows its type,
    /// `(x y : α)` (a type ascription of the names), `{x y : α}`, `⦃x y : α⦄`, and an instance
    /// binder `[inst : C α]` when it is dependent and the printed rest names it, `[C α]`
    /// otherwise. A binder is grouped with the next when their binder infos agree, neither is an
    /// instance binder, and the next one's domain is this one's (`shouldGroupWithNext`).
    fn typed_lambda(&mut self, e: &Expr, outer: u32) -> Doc {
        struct Group {
            info: BinderInfo,
            names: Vec<String>,
            first: usize,
            type_: Format,
            dependent: bool,
        }
        let depth = self.names.len();
        let mut groups: Vec<Group> = Vec::new();
        let mut body = e;
        while let ExprNode::Lam {
            binder_name: name,
            binder_type,
            body: inner,
            binder_info,
        } = body.node()
        {
            if internal_name(name) {
                self.unbind_to(depth);
                return Err(INTERNAL_BINDER);
            }
            let type_ = match self.with_trailing(false, |printer| printer.doc(binder_type, 0)) {
                Ok(type_) => type_,
                Err(error) => {
                    self.unbind_to(depth);
                    return Err(error);
                }
            };
            let first = self.names.len();
            let shown = self.bound_name(name, inner);
            self.bind(shown.clone(), binder_type);
            let mut names = vec![shown];
            let mut dependent = inner.has_loose_bvar(0);
            let mut domain = binder_type.clone();
            let mut next = inner;
            while *binder_info != BinderInfo::InstImplicit
                && let ExprNode::Lam {
                    binder_name: other,
                    binder_type: other_type,
                    body: other_body,
                    binder_info: other_info,
                } = next.node()
                && other_info == binder_info
                && domain
                    .lift_loose(0, 1)
                    .is_ok_and(|lifted| lifted == *other_type)
            {
                if internal_name(other) {
                    self.unbind_to(depth);
                    return Err(INTERNAL_BINDER);
                }
                let shown = self.bound_name(other, other_body);
                self.bind(shown.clone(), other_type);
                names.push(shown);
                dependent |= other_body.has_loose_bvar(0);
                domain = other_type.clone();
                next = other_body;
            }
            groups.push(Group {
                info: *binder_info,
                names,
                first,
                type_,
                dependent,
            });
            body = next;
        }
        let trailing = self.trailing && outer == 0;
        let printed = self.with_trailing(trailing, |printer| printer.doc(body, 0));
        let named: Vec<bool> = groups
            .iter()
            .map(|group| group.dependent && self.shown.get(group.first) == Some(&true))
            .collect();
        self.unbind_to(depth);
        let printed = printed?;
        let mut binders = Format::Nil;
        for (group, named) in groups.into_iter().zip(named) {
            let binder = match group.info {
                // `($stxCurNames : $T)`: the names are one application node when there are two
                // or more.
                BinderInfo::Default => {
                    let mut names = Format::Nil;
                    for (index, name) in group.names.iter().enumerate() {
                        if index > 0 {
                            names = names.then(Format::Line);
                        }
                        names = names.then(Format::text(name.clone()));
                    }
                    let names = if group.names.len() > 1 {
                        node(names)
                    } else {
                        names
                    };
                    node(
                        Format::text("(")
                            .then(names)
                            .then(Format::text(" :"))
                            .then(Format::Line)
                            .then(group.type_)
                            .then(Format::text(")")),
                    )
                }
                info => self.binder_group(info, &group.names, group.type_, !named, None),
            };
            binders = binders.then(Format::Line).then(binder);
        }
        let fun = Format::text("fun")
            .then(node(binders.then(Format::text(" =>"))))
            .then(Format::Line)
            .then(printed);
        Ok(if outer >= MAX_PREC || self.trailing {
            node(Format::text("(").then(fun).then(Format::text(")")))
        } else {
            fun
        })
    }

    fn pi_tail(&mut self, e: &Expr) -> Doc {
        self.doc(e, ARROW_PREC)
    }

    /// `#check c` for a constant: `c binders : type` (`delabConstWithSignature`), the
    /// leading binders with accessible names shown before the colon, grouped.
    pub fn signature(&mut self, name: &Name, type_: &Expr) -> Printed {
        if self.pp.private_names && is_private(name) {
            return Err(Unsupported("a private name under `pp.privateNames`"));
        }
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
            // `delabParamsAux`: an explicit parameter with a default is `(x : α := v)`. One with
            // a tactic is `(h : p := by tac)`, the tactic read by evaluating its syntax constant,
            // which this door does not do.
            if *binder_info == BinderInfo::Default && annotation(binder_type, "autoParam").is_some()
            {
                self.unbind_to(depth);
                return Err(Unsupported("a parameter whose default is a tactic"));
            }
            let (type_doc, default) = match annotation(binder_type, "optParam") {
                Some((domain, value)) if *binder_info == BinderInfo::Default => {
                    (self.doc(domain, 0)?, Some(self.doc(value, 0)?))
                }
                _ => (self.doc(binder_type, 0)?, None),
            };
            let type_text = flat(&self.doc(binder_type, 0)?);
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
            groups.push(self.binder_group(*binder_info, &names, type_doc, hidden, default));
            current = next;
        }
        // `processSpine`: after the colon, the type's spine shows its accessible binder names.
        self.spine_names = matches!(current.node(), ExprNode::ForallE { .. });
        let rest = self.doc(current, 0);
        self.spine_names = false;
        self.unbind_to(depth);
        // The signature names the constant's universe parameters (`List.map.{u_1, u_2}`).
        let parameters = self
            .env
            .find(name)
            .map(|info| info.constant_val().level_params.clone())
            .unwrap_or_default();
        // `delabConstWithSignature` heads the signature with the whole name.
        let head = if parameters.is_empty() {
            self.full_name(name)
        } else {
            format!(
                "{}.{{{}}}",
                self.full_name(name),
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

    /// Notations in the pin's `#check` output (v4.32.0, measured 2026-10-20 on the upstream
    /// `1571`, `binder_predicates`, `decimals`, `negFloat`, `fun` and `mathport_issue16`
    /// tests): `∃` with merged binders, bracketed only as an argument or where an operator
    /// follows it; `-`; scientific literals; `∘`; and `()`.
    #[test]
    fn exists_negation_literals_composition_and_unit_print_as_the_pins_notations() {
        let env = Environment::new();
        let constant = |parts: &[&str]| Expr::const_(name(parts), Vec::new());
        let nat = || constant(&["Nat"]);
        let var = |i| Expr::bvar(i).unwrap();
        let apply = |head: Expr, args: Vec<Expr>| args.into_iter().fold(head, Expr::app);
        let literal = |n| Expr::lit(Literal::Nat(NatLit::from_u64(n)));
        let eq = |a, b| apply(constant(&["Eq"]), vec![nat(), a, b]);
        let exists = |binder: &str, body| {
            apply(
                constant(&["Exists"]),
                vec![
                    nat(),
                    Expr::lam(name(&[binder]), nat(), body, BinderInfo::Default),
                ],
            )
        };
        let arrow =
            |domain, body| Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default);
        let truth = || constant(&["True"]);
        let mut printer = Printer::new(&env);
        let mut shown = |e: &Expr| printer.expr(e, 0).unwrap();
        let reflexive = exists("a", eq(var(0), var(0)));
        assert_eq!(shown(&reflexive), "∃ a, a = a");
        assert_eq!(
            shown(&exists("x", exists("y", eq(var(1), var(0))))),
            "∃ x y, x = y"
        );
        assert_eq!(
            shown(&arrow(truth(), reflexive.clone())),
            "True → ∃ a, a = a"
        );
        assert_eq!(
            shown(&arrow(reflexive.clone(), truth())),
            "(∃ a, a = a) → True"
        );
        let and = |a, b| apply(constant(&["And"]), vec![a, b]);
        assert_eq!(
            shown(&and(reflexive.clone(), truth())),
            "(∃ a, a = a) ∧ True"
        );
        assert_eq!(shown(&and(truth(), reflexive.clone())), "True ∧ ∃ a, a = a");
        assert_eq!(
            shown(&Expr::app(constant(&["P"]), reflexive)),
            "P (∃ a, a = a)"
        );
        let scientific = |mantissa, negative: bool, exponent| {
            let sign = if negative { "true" } else { "false" };
            apply(
                constant(&["OfScientific", "ofScientific"]),
                vec![
                    constant(&["Float"]),
                    constant(&["instOfScientificFloat"]),
                    literal(mantissa),
                    constant(&["Bool", sign]),
                    literal(exponent),
                ],
            )
        };
        for (mantissa, negative, exponent, expected) in [
            (12, true, 1, "1.2"),
            (10, true, 1, "1.0"),
            (1, true, 0, "1."),
            (31416, true, 4, "3.1416"),
            (12, true, 2, "0.12"),
            (12, true, 3, "12e-3"),
            (12, false, 3, "12e3"),
        ] {
            assert_eq!(shown(&scientific(mantissa, negative, exponent)), expected);
        }
        let negate = |operand| {
            apply(
                constant(&["Neg", "neg"]),
                vec![
                    constant(&["Int"]),
                    constant(&["Int", "instNegInt"]),
                    operand,
                ],
            )
        };
        assert_eq!(shown(&negate(literal(42))), "-42");
        assert_eq!(shown(&negate(scientific(420, true, 1))), "-42.0");
        let compose = |f, g| {
            apply(
                constant(&["Function", "comp"]),
                vec![nat(), nat(), constant(&["Bool"]), f, g],
            )
        };
        assert_eq!(
            shown(&compose(
                constant(&["f"]),
                compose(constant(&["g"]), constant(&["g"]))
            )),
            "f ∘ g ∘ g"
        );
        assert_eq!(shown(&constant(&["Unit", "unit"])), "()");
    }
}
