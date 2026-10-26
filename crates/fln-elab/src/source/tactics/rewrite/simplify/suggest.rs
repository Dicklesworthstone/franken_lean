//! `simp?` and `simp_all?` (vendored `src/Lean/Elab/Tactic/SimpTrace.lean`): the tactic is
//! `simp` (`simp_all`), and it logs the equivalent `simp only` call (`mkSimpOnly`,
//! `src/Lean/Elab/Tactic/Simp.lean:618-669`) as `Try this:` (`addSuggestion`,
//! `src/Lean/Meta/Tactic/TryThis.lean:92-103`).
//!
//! The rewriting, and with it the verdict and the goals left, are this engine's simplifier's,
//! unchanged. The suggestion lists what the *pin's* simplifier records in `UsedSimps`, in its
//! insertion order: which theorem rewrites a term, and when, follows the pin's traversal
//! (`Simp.simpLoop`, `src/Lean/Meta/Tactic/Simp/Main.lean:654-686`: `pre`, `reduceStep`, the
//! congruence over the arguments, `post`, again until nothing changes, memoized), its rule
//! choice (`rewrite?`, `src/Lean/Meta/Tactic/Simp/Rewrite.lean:226-262`: the discrimination
//! tree's candidates by priority, the first that unifies and whose premises discharge), and its
//! discharger (`dischargeDefault?`, `Rewrite.lean:596-610`, which simplifies the premise and
//! keeps what it used only on success). That is modeled here over a stated fragment, run
//! on its own snapshot of the elaboration state, and checked against what this engine's
//! simplifier actually left; anywhere outside it, or where the two disagree, the tactic is a
//! typed refusal ([`TacticError::SimpSuggestionUnsupported`]), never a guessed suggestion.
//!
//! Outside the fragment, measured or read at v4.32.0: configurations, dischargers, `!`,
//! `dsimp?`; term, `↓`/`↑` and projection arguments; any node whose head is a lambda, a let,
//! a projection, a matcher or recursor, a binder other than a non-dependent arrow, `ite`/`dite`
//! or another head with a simplification procedure or congruence theorem the model does not
//! reproduce; rules that leave parameters open, conditional permutation rules, rules whose
//! pattern unfolds at reducible transparency where their order decides; and `simp_all?` with a
//! propositional hypothesis. A permutation rule rewrites only where the pin's `acLt` admits it
//! (`aclt.rs`).
use super::*;

/// The pin's `Simp.Config.maxDischargeDepth`.
const MAX_DISCHARGE_DEPTH: u32 = 2;
/// Visits this model follows before it stops, far below the pin's `maxSteps`.
const MAX_SIMULATION_STEPS: usize = 1 << 14;
/// Nested visits this model follows on the native stack before it stops.
const MAX_SIMULATION_NESTING: usize = 128;
/// The pin's `format.width`.
const WIDTH: usize = 120;

fn refuse<T>(reason: &'static str) -> Result<T, NatDefinitionElabError> {
    Err(error(TacticError::SimpSuggestionUnsupported(reason)))
}

fn named(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

/// Heads with a `@[congr]` theorem (`getSimpCongrTheorems`), measured at v4.32.0 under
/// `import Lean` (a superset of `Init`'s): the pin's `congr` tries those before the automatic
/// congruence this model reproduces.
const CONGRUENCE_HEADS: &[&str] = &[
    "Array.all",
    "Array.allM",
    "Array.any",
    "Array.anyM",
    "Array.extract",
    "Array.filter",
    "Array.filterM",
    "Array.filterMap",
    "Array.filterMapM",
    "Array.filterRevM",
    "Array.flatMapM",
    "Array.foldl",
    "Array.foldlM",
    "Array.foldr",
    "Array.foldrM",
    "Array.mapFinIdx",
    "Exists",
    "Fin.foldl",
    "Fin.foldlM",
    "Fin.foldr",
    "Fin.foldrM",
    "ForIn'.forIn'",
    "ForIn.forIn",
    "ForM.forM",
    "List.mapFinIdx",
    "Nat.dfoldRev",
    "Option.guard",
    "Option.pbind",
    "Option.pelim",
    "Option.pfilter",
    "Option.pmap",
    "Std.Iterators.HetT.pmap",
    "Std.Iterators.HetT.prun",
    "Vector.all",
    "Vector.allM",
    "Vector.any",
    "Vector.anyM",
    "Vector.findFinIdx?",
    "Vector.foldl",
    "Vector.foldr",
    "Vector.mapFinIdx",
    "Vector.mapM",
    "dite",
    "ite",
];

/// Heads of the default pre simplification procedures (`reduceIte`, `reduceDIte` and their
/// `dsimprocs`, `Char.isValue`), and of the one pre theorem `Init` registers
/// (`binderNameHint.eq_1`), with `wfParam`, which the well-founded `dsimprocs` read.
const PRE_HEADS: &[&str] = &["ite", "dite", "Char.ofNat", "binderNameHint", "wfParam"];

/// Root keys of the default post simplification procedures not modeled by head and operand
/// below, measured at v4.32.0 (`getSimprocs`, `getSimprocDeclKeys?`): at such a head a
/// procedure may fire, so the model stops.
const SIMPROC_HEADS: &[&str] = &[
    "BitVec.abs",
    "BitVec.allOnes",
    "BitVec.clz",
    "BitVec.cpop",
    "BitVec.extractLsb'",
    "BitVec.getLsbD",
    "BitVec.getMsbD",
    "BitVec.ofFin",
    "BitVec.ofInt",
    "BitVec.ofNat",
    "BitVec.replicate",
    "BitVec.rotateLeft",
    "BitVec.rotateRight",
    "BitVec.sdiv",
    "BitVec.setWidth",
    "BitVec.setWidth'",
    "BitVec.shiftLeft",
    "BitVec.shiftLeftZeroExtend",
    "BitVec.signExtend",
    "BitVec.sle",
    "BitVec.slt",
    "BitVec.smod",
    "BitVec.smtSDiv",
    "BitVec.smtUDiv",
    "BitVec.srem",
    "BitVec.sshiftRight",
    "BitVec.toInt",
    "BitVec.toNat",
    "BitVec.udiv",
    "BitVec.ule",
    "BitVec.ult",
    "BitVec.umod",
    "BitVec.ushiftRight",
    "BitVec.toFin",
    "cast",
    "Char.isAlpha",
    "Char.isAlphanum",
    "Char.isDigit",
    "Char.isLower",
    "Char.isUpper",
    "Char.isWhitespace",
    "Char.ofNatAux",
    "Char.toLower",
    "Char.toNat",
    "Char.toUpper",
    "Char.val",
    "Complement.complement",
    "Fin.addNat",
    "Fin.castAdd",
    "Fin.castLE",
    "Fin.castLT",
    "Fin.castSucc",
    "Fin.last",
    "Fin.mk",
    "Fin.natAdd",
    "Fin.ofNat",
    "Fin.pred",
    "Fin.rev",
    "Fin.subNat",
    "Fin.succ",
    "GetElem?.getElem!",
    "GetElem?.getElem?",
    "GetElem.getElem",
    "Inhabited.default",
    "Int16.ofInt",
    "Int16.ofIntLE",
    "Int16.ofNat",
    "Int16.toInt",
    "Int16.toNatClampNeg",
    "Int32.ofInt",
    "Int32.ofIntLE",
    "Int32.ofNat",
    "Int32.toInt",
    "Int32.toNatClampNeg",
    "Int64.ofInt",
    "Int64.ofIntLE",
    "Int64.ofNat",
    "Int64.toInt",
    "Int64.toNatClampNeg",
    "Int8.ofInt",
    "Int8.ofIntLE",
    "Int8.ofNat",
    "Int8.toInt",
    "Int8.toNatClampNeg",
    "Int.bdiv",
    "Int.bmod",
    "Int.fdiv",
    "Int.fmod",
    "Int.natAbs",
    "Int.negSucc",
    "Int.ofNat",
    "Int.tdiv",
    "Int.tmod",
    "Int.toNat",
    "ISize.toInt",
    "ISize.toNatClampNeg",
    "List.replicate",
    "NatCast.natCast",
    "Nat.gcd",
    "String.ofList",
    "String.push",
    "String.singleton",
    "String.toList",
    "ToString.toString",
    "UInt16.ofNat",
    "UInt16.ofNatLT",
    "UInt16.toNat",
    "UInt32.ofNat",
    "UInt32.ofNatLT",
    "UInt32.toNat",
    "UInt64.ofNat",
    "UInt64.ofNatLT",
    "UInt64.toNat",
    "UInt8.ofNat",
    "UInt8.ofNatLT",
    "UInt8.toNat",
    "USize.toNat",
];

/// Types with literal simplification procedures (`reduceEq`, `reduceAdd`, … for each).
const LITERAL_TYPES: &[&str] = &[
    "Int", "Fin", "Char", "String", "BitVec", "UInt8", "UInt16", "UInt32", "UInt64", "USize",
    "Int8", "Int16", "Int32", "Int64", "ISize",
];

/// The binary operators whose `Nat` instances `Nat.reduceBin` evaluates, and the procedure
/// that records the evaluation (`BuiltinSimprocs/Nat.lean:52-56`). Others are not evaluated.
const NAT_BINARY: &[(&str, &str)] = &[
    ("HAdd.hAdd", "Nat.reduceAdd"),
    ("HMul.hMul", "Nat.reduceMul"),
    ("HSub.hSub", "Nat.reduceSub"),
    ("HDiv.hDiv", "Nat.reduceDiv"),
    ("HMod.hMod", "Nat.reduceMod"),
];

const ARITHMETIC_HEADS: &[&str] = &[
    "HAdd.hAdd",
    "HSub.hSub",
    "HMul.hMul",
    "HDiv.hDiv",
    "HMod.hMod",
    "HPow.hPow",
    "HAnd.hAnd",
    "HOr.hOr",
    "HXor.hXor",
    "HShiftLeft.hShiftLeft",
    "HShiftRight.hShiftRight",
];

const RELATION_HEADS: &[&str] = &["LT.lt", "LE.le", "GT.gt", "GE.ge", "BEq.beq", "bne"];

/// One entry of the pin's `UsedSimps`, as `mkSimpOnly` reads it.
#[derive(Clone, Debug, PartialEq)]
enum Used {
    /// `.decl name (post := true) inv`.
    Decl { name: Name, inv: bool },
    /// A builtin simplification procedure.
    Simproc(Name),
    /// `.stx`: an argument of the call, printed as written.
    Stx(String),
    /// `.fvar`: a local, which `mkSimpOnly` appends after the rest.
    Fvar(FVarId),
}

#[derive(Clone)]
struct Candidate<'a> {
    rule: SimpRule<'a>,
    origin: Used,
    priority: u32,
    /// Its place in the pin's discrimination-tree leaf: the default set in registration order,
    /// then the call's arguments, in order.
    order: usize,
    /// `mkSimpTheoremFromExpr`'s `noIndexAtArgs`: a local or `[*]` hypothesis.
    no_index: bool,
}

struct Simulation<'a> {
    candidates: Vec<Candidate<'a>>,
    /// The let variables the call names (`zetaDeltaSet`).
    zeta: Vec<FVarId>,
    /// Definitions unfolded by name (`toUnfold`).
    unfold: Vec<Name>,
    /// The hypothesis being simplified, whose `[*]` theorem the pin erases (`simpGoal`).
    excluded: Option<FVarId>,
    used: Vec<Used>,
    /// Named let variables the pin's unifier unfolded (`zetaDeltaFVarIds`), recorded at the
    /// end of the run (`updateUsedSimpsWithZetaDelta`).
    tracked: Vec<FVarId>,
    cache: HashMap<Expr, Expr>,
    depth: u32,
    steps: usize,
    nesting: usize,
    contextual: bool,
}

impl Simulation<'_> {
    fn record(&mut self, origin: Used) {
        if !self.used.contains(&origin) {
            self.used.push(origin);
        }
    }
}

/// What the run must have left for the suggestion to describe it.
struct Expected {
    closed: bool,
    target: Expr,
    /// Each simulated hypothesis's simplified type, by name.
    hypotheses: Vec<(Name, Expr)>,
}

/// A congruence argument's role (`CongrArgKind`): rewritten, left for `dsimp`, or untouched.
#[derive(Clone, Copy, PartialEq)]
enum ArgKind {
    Eq,
    Fixed,
    Keep,
}

/// A discrimination-tree key (`DiscrTree.Key`).
#[derive(Clone, Debug, PartialEq)]
enum Key {
    Star,
    Other,
    Arrow,
    Lit(Literal),
    Const(Name, usize),
    FVar(FVarId, usize),
}

fn mentions(expr: &Expr, id: &FVarId) -> bool {
    let mut pending = vec![expr];
    while let Some(term) = pending.pop() {
        if matches!(term.node(), ExprNode::FVar { id: found } if found == id) {
            return true;
        }
        pending.extend(children(term).into_iter().flatten());
    }
    false
}

fn spine(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut head = expr;
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

fn head_name(expr: &Expr) -> Option<&Name> {
    match spine(expr).0.node() {
        ExprNode::Const { name, .. } => Some(name),
        _ => None,
    }
}

fn is_const(expr: &Expr, text: &str) -> bool {
    matches!(expr.node(), ExprNode::Const { name, .. } if *name == named(text))
}

fn in_list(name: &Name, list: &[&str]) -> bool {
    list.iter().any(|text| *name == named(text))
}

/// `getNatValue?`: a raw literal or `OfNat.ofNat Nat n _`.
fn nat_value(expr: &Expr) -> Option<u64> {
    match expr.node() {
        ExprNode::Lit {
            literal: Literal::Nat(n),
        } => n.to_u64(),
        _ => {
            let (head, args) = spine(expr);
            if !is_const(head, "OfNat.ofNat") || args.len() != 3 || !is_const(args[0], "Nat") {
                return None;
            }
            match args[1].node() {
                ExprNode::Lit {
                    literal: Literal::Nat(n),
                } => n.to_u64(),
                _ => None,
            }
        }
    }
}

/// A literal any type's simplification procedures read: a numeral, `Int.ofNat`/`Int.negSucc`,
/// a negated numeral, a string or a character.
fn literal_like(mut expr: &Expr) -> bool {
    // `-(-…n)`, peeled without recursion.
    loop {
        let (head, args) = spine(expr);
        if is_const(head, "Neg.neg") && args.len() == 3 {
            expr = args[2];
        } else {
            break;
        }
    }
    if matches!(expr.node(), ExprNode::Lit { .. }) {
        return true;
    }
    let (head, args) = spine(expr);
    let Some(name) = head_name(head) else {
        return false;
    };
    (*name == named("OfNat.ofNat") && args.len() == 3)
        || in_list(
            name,
            &[
                "Int.ofNat",
                "Int.negSucc",
                "Char.ofNat",
                "Nat.zero",
                "Nat.succ",
            ],
        )
}

/// `NatOffset.fromExpr?` succeeds: a numeral, or an offset by a numeral (`x + k`, `Nat.add x k`,
/// `Nat.succ x`). A superset is fine: it only stops the model.
fn nat_offset_or_literal(expr: &Expr) -> bool {
    if literal_like(expr) {
        return true;
    }
    let (head, args) = spine(expr);
    let Some(name) = head_name(head) else {
        return false;
    };
    match name.to_display_string().as_str() {
        "HAdd.hAdd" if args.len() == 6 => literal_like(args[5]),
        "Add.add" if args.len() == 4 => literal_like(args[3]),
        "Nat.add" if args.len() == 2 => literal_like(args[1]),
        "Nat.succ" => true,
        _ => false,
    }
}

/// The discrimination tree's `isNumeral`/`toNatLit?` (`DiscrTree/Main.lean:121-160`): a raw
/// literal, `Nat.zero`, `Nat.succ` of a numeral, or `OfNat.ofNat _ n _` of a numeral.
fn key_numeral(mut expr: &Expr) -> Option<u64> {
    let mut successors: u64 = 0;
    loop {
        if let ExprNode::Lit {
            literal: Literal::Nat(n),
        } = expr.node()
        {
            return n.to_u64()?.checked_add(successors);
        }
        let (head, args) = spine(expr);
        let name = head_name(head)?;
        match (name.to_display_string().as_str(), args.len()) {
            ("Nat.zero", 0) => return Some(successors),
            ("Nat.succ", 1) => {
                successors = successors.checked_add(1)?;
                expr = args[0];
            }
            ("OfNat.ofNat", 3) => expr = args[1],
            _ => return None,
        }
    }
}

/// The discrimination tree's `isOffset` (`DiscrTree/Main.lean:166-181`), a `*` key below the
/// root: `Nat.add _ k`, `Add.add Nat _ _ k`, `HAdd.hAdd _ Nat _ _ _ k` with a numeral `k`, or
/// `Nat.succ _`.
fn key_offset(expr: &Expr) -> bool {
    let (head, args) = spine(expr);
    let Some(name) = head_name(head) else {
        return false;
    };
    match (name.to_display_string().as_str(), args.len()) {
        ("Nat.add", 2) => key_numeral(args[1]).is_some(),
        ("Add.add", 4) => is_const(args[0], "Nat") && key_numeral(args[3]).is_some(),
        ("HAdd.hAdd", 6) => is_const(args[1], "Nat") && key_numeral(args[5]).is_some(),
        ("Nat.succ", 1) => true,
        _ => false,
    }
}

fn literal_type(expr: &Expr) -> bool {
    head_name(expr).is_some_and(|name| in_list(name, LITERAL_TYPES))
}

/// `mkNatLit n`: `@OfNat.ofNat Nat n (instOfNatNat n)`.
fn nat_literal(value: u64) -> Expr {
    let raw = Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)));
    app(
        Expr::const_(named("OfNat.ofNat"), vec![Level::zero()]),
        [
            Expr::const_(named("Nat"), Vec::new()),
            raw.clone(),
            Expr::app(Expr::const_(named("instOfNatNat"), Vec::new()), raw),
        ],
    )
}

/// An identifier the pin's formatter prints as it is, without `«»`.
fn plain_identifier(text: &str) -> bool {
    let mut chars = text.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_alphabetic() || first == '_')
        && chars.all(|c| {
            c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?' | '\u{2080}'..='\u{2089}')
        })
        && !matches!(
            text,
            "at" | "by"
                | "do"
                | "fun"
                | "have"
                | "if"
                | "in"
                | "let"
                | "then"
                | "else"
                | "show"
                | "from"
                | "with"
                | "match"
                | "using"
                | "only"
        )
}

/// `name` as the pin's formatter prints an identifier, or `None` where it would escape it.
fn printable(name: &Name) -> Option<String> {
    let parts = scope::components(name).ok()?;
    if parts.is_empty() || !parts.iter().all(|part| plain_identifier(part)) {
        return None;
    }
    Some(parts.join("."))
}

impl Context {
    /// `simp?` and `simp_all?`: this engine's `simp`/`simp_all`, then the pin's suggestion.
    pub(in crate::source) fn simp_trace_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        kind: &Name,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let simp_all = kind == &parser_kind(&["Tactic", "simpAllTrace"]);
        let dsimp = kind == &parser_kind(&["Tactic", "dsimpTrace"]);
        let (syntax, word, rest_kind, slots) = if simp_all {
            ("simpAllTrace", "simp_all?", "simpAllTraceArgsRest", 4)
        } else if dsimp {
            ("dsimpTrace", "dsimp?", "dsimpTraceArgsRest", 4)
        } else {
            ("simpTrace", "simp?", "simpTraceArgsRest", 5)
        };
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", syntax])?;
        let [keyword, bang, rest] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, word, "simp suggestion keyword")?;
        if dsimp {
            return refuse("`dsimp?`");
        }
        if !expect_null_args(bang, "simp suggestion `!`")?.is_empty() {
            return refuse("`simp?!`, which unfolds definitions automatically");
        }
        let rest = expect_node(
            rest,
            &parser_kind(&["Tactic", rest_kind]),
            slots,
            "simp suggestion arguments",
        )?;
        // `simp` writes its rule list inline where `simp?` has its own `simpArgs` node.
        let list_kind = parser_kind(&["Tactic", if simp_all { "dsimpArgs" } else { "simpArgs" }]);
        let inline = match expect_null_args(&rest[3], "optional simp rule list")? {
            [] => rest[3].clone(),
            [Syntax::Node { kind, args, .. }] if *kind == list_kind && args.len() == 3 => {
                Syntax::node(Name::from_components(["null"]), args.clone())
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let mut simp_args = vec![
            Syntax::Atom {
                info: keyword.info(),
                val: if simp_all { "simp_all" } else { "simp" }.to_string(),
            },
            rest[0].clone(),
            rest[1].clone(),
            rest[2].clone(),
            inline,
        ];
        if !simp_all {
            simp_args.push(rest[4].clone());
        }
        // The simulation reads the state the tactic started from.
        let initial = self.rewrite_trial();
        let before = proof.work.len();
        if simp_all {
            self.simplify_all_proof_goal(proof, goal.clone(), &simp_args)?;
        } else {
            self.simplify_proof_goal(proof, goal.clone(), &simp_args)?;
        }
        let mut left = Vec::new();
        for work in &proof.work[before..] {
            if let Work::Goal(next) = work {
                left.push(next.clone());
            }
        }
        if left.len() > 1 {
            return refuse("a simplification that left more than one goal");
        }
        let base = initial.txn.budget.heartbeats_consumed;
        let mut simulation = initial;
        let outcome = simulation.simp_suggestion(&goal, &simp_args, simp_all);
        let spent = simulation
            .txn
            .budget
            .heartbeats_consumed
            .saturating_sub(base);
        self.txn.budget.heartbeats_consumed =
            self.txn.budget.heartbeats_consumed.saturating_add(spent);
        self.tick()?;
        let (message, expected) = outcome?;
        self.check_simulated_outcome(&goal, left.first(), &expected)?;
        let at = keyword.info().pos(true).map_or(0, |p| p.0);
        self.log_info(at, message)
    }

    /// The model and this engine's run must have left the same goal, up to its locals' types.
    fn check_simulated_outcome(
        &mut self,
        goal: &ProofGoal,
        left: Option<&ProofGoal>,
        expected: &Expected,
    ) -> Result<(), NatDefinitionElabError> {
        let disagree = || refuse("a simplification this model reproduces differently");
        let Some(left) = left else {
            return if expected.closed { Ok(()) } else { disagree() };
        };
        if expected.closed {
            return disagree();
        }
        if self.instantiate(&left.target)? != expected.target {
            return disagree();
        }
        for local in goal.lctx.decls() {
            self.tick()?;
            if local.user_name.is_anonymous()
                || goal
                    .lctx
                    .find_by_user_name(&local.user_name)
                    .is_none_or(|visible| visible.id != local.id)
            {
                continue;
            }
            let wanted = match expected
                .hypotheses
                .iter()
                .find(|(name, _)| *name == local.user_name)
            {
                Some((_, type_)) => type_.clone(),
                None => self.instantiate(&local.type_)?,
            };
            let Some(now) = left.lctx.find_by_user_name(&local.user_name).cloned() else {
                return disagree();
            };
            if self.instantiate(&now.type_)? != wanted {
                return disagree();
            }
        }
        Ok(())
    }

    /// The pin's suggestion for `simp`/`simp_all` with `args`, and what the run must leave.
    fn simp_suggestion(
        &mut self,
        goal: &ProofGoal,
        args: &[Syntax],
        simp_all: bool,
    ) -> Result<(String, Expected), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let (config, discharger, only, arguments, location) = match args {
            [_, config, discharger, only, arguments] => (config, discharger, only, arguments, None),
            [_, config, discharger, only, arguments, location] => {
                (config, discharger, only, arguments, Some(location))
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let config = expect_node(
            config,
            &parser_kind(&["Tactic", "optConfig"]),
            1,
            "simp configuration",
        )?;
        if !expect_null_args(&config[0], "simp configuration items")?.is_empty() {
            return refuse("a simp configuration");
        }
        if !expect_null_args(discharger, "simp discharger")?.is_empty() {
            return refuse("a discharger");
        }
        let only = !expect_null_args(only, "optional explicit simp set")?.is_empty();
        let target = self.instantiate(&goal.target)?;
        // The locations, in `simpGoal`'s order, and how the call prints them.
        let (hypotheses, simplify_target, suffix) = match location {
            None => (Vec::new(), true, String::new()),
            Some(location) => match self.rewrite_locations(location)? {
                None => (Vec::new(), true, String::new()),
                Some(locations) if locations.all => (
                    self.simulated_nondependent_hypotheses(goal, &target)?,
                    true,
                    " at *".to_string(),
                ),
                Some(locations) => {
                    let mut ids = Vec::new();
                    let mut shown = String::from(" at");
                    for name in &locations.hypotheses {
                        self.tick()?;
                        let Some(local) = goal.lctx.find_by_user_name(name) else {
                            return Err(error(TacticError::RewriteLocation));
                        };
                        if local.value.is_some() || !self.simulated_proposition(&local.type_)? {
                            return refuse("a location that is not a hypothesis");
                        }
                        let Some(text) = printable(name) else {
                            return refuse("a location name the pin would escape");
                        };
                        shown.push(' ');
                        shown.push_str(&text);
                        ids.push(local.id.clone());
                    }
                    if locations.target {
                        shown.push_str(" ⊢");
                    }
                    (ids, locations.target, shown)
                }
            },
        };
        let (mut simulation, statements) = self.simulated_rule_set(only, arguments, simp_all)?;
        if simp_all {
            for local in goal.lctx.decls() {
                self.tick()?;
                if local.value.is_none()
                    && !self.is_matrix_hypothesis(local)
                    && self.simulated_proposition(&local.type_)?
                {
                    return refuse("`simp_all?` with a propositional hypothesis");
                }
            }
        }
        let mut expected = Expected {
            closed: false,
            target: target.clone(),
            hypotheses: Vec::new(),
        };
        for id in &hypotheses {
            let local = goal
                .lctx
                .find(id)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let type_ = self.instantiate(&local.type_)?;
            simulation.excluded = Some(id.clone());
            let simplified = self.simulated_run(&mut simulation, goal, &type_, &statements)?;
            if is_const(&simplified, "False") {
                expected.closed = true;
                break;
            }
            expected
                .hypotheses
                .push((local.user_name.clone(), simplified));
        }
        if simplify_target && !expected.closed {
            simulation.excluded = None;
            let simplified = self.simulated_run(&mut simulation, goal, &target, &statements)?;
            if is_const(&simplified, "True") {
                expected.closed = true;
            }
            expected.target = simplified;
        }
        let message = self.simulated_message(&simulation, goal, simp_all, &suffix)?;
        Ok((message, expected))
    }

    fn simulated_proposition(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(sort) = self.known_type(type_)? else {
            return Ok(false);
        };
        let sort = self.whnf(&sort)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.normalize().is_zero()))
    }

    /// `getNondepPropHyps` (`src/Lean/Meta/Tactic/Util.lean:98-125`).
    fn simulated_nondependent_hypotheses(
        &mut self,
        goal: &ProofGoal,
        target: &Expr,
    ) -> Result<Vec<FVarId>, NatDefinitionElabError> {
        let mut candidates: Vec<FVarId> = Vec::new();
        let remove = |expr: &Expr, candidates: &mut Vec<FVarId>| {
            let mut pending = vec![expr.clone()];
            while let Some(term) = pending.pop() {
                if let ExprNode::FVar { id } = term.node() {
                    candidates.retain(|candidate| candidate != id);
                }
                pending.extend(children(&term).into_iter().flatten().cloned());
            }
        };
        for local in goal.lctx.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) {
                continue;
            }
            let type_ = self.instantiate(&local.type_)?;
            remove(&type_, &mut candidates);
            if let Some(value) = &local.value {
                let value = self.instantiate(value)?;
                remove(&value, &mut candidates);
            }
            if local.value.is_none() && self.simulated_proposition(&type_)? {
                candidates.push(local.id.clone());
            }
        }
        remove(target, &mut candidates);
        Ok(candidates)
    }

    /// The pin's simp set for this call (`mkSimpContext`, `elabSimpArgs`,
    /// `src/Lean/Elab/Tactic/Simp.lean:410-495`), with each explicit rule's statement.
    fn simulated_rule_set<'a>(
        &mut self,
        only: bool,
        arguments: &'a Syntax,
        simp_all: bool,
    ) -> Result<(Simulation<'a>, Vec<Expr>), NatDefinitionElabError> {
        let mut simulation = Simulation {
            candidates: Vec::new(),
            zeta: Vec::new(),
            unfold: Vec::new(),
            excluded: None,
            used: Vec::new(),
            tracked: Vec::new(),
            cache: HashMap::new(),
            depth: 0,
            steps: 0,
            nesting: 0,
            contextual: simp_all,
        };
        let mut statements = Vec::new();
        if only {
            // `simpOnlyBuiltins` (`Simp.lean:512`), the first entries of the fresh set.
            for (order, text) in ["eq_self", "iff_self"].into_iter().enumerate() {
                let name = named(text);
                if !self.txn.env.contains(&name) {
                    return refuse("`simp only` without `eq_self` and `iff_self`");
                }
                simulation.candidates.push(Candidate {
                    rule: SimpRule::Global(scope::simp::SimpEntry {
                        declaration: name.clone(),
                        proof: None,
                        priority: 1000,
                        reverse: false,
                        order,
                    }),
                    origin: Used::Decl { name, inv: false },
                    priority: 1000,
                    order,
                    no_index: false,
                });
            }
        } else {
            let mut rules = scope::simp::read(&self.txn.env)
                .map_err(|e| failure(SourceInferenceError::SimpSet(e)))?;
            for local in &self.source_scope.local_simp {
                if !rules
                    .iter()
                    .any(|rule| rule.declaration == local.declaration)
                {
                    rules.push(local.clone());
                }
            }
            for entry in rules {
                self.tick()?;
                let definition = entry.proof.is_none()
                    && matches!(
                        self.txn.env.find(&entry.declaration),
                        Some(ConstantInfo::Defn(_))
                    );
                if definition {
                    if entry.reverse {
                        return refuse("a reversed definition in the default set");
                    }
                    simulation.unfold.push(entry.declaration.clone());
                    continue;
                }
                simulation.candidates.push(Candidate {
                    origin: Used::Decl {
                        name: entry.declaration.clone(),
                        inv: entry.reverse,
                    },
                    priority: entry.priority,
                    order: entry.order,
                    no_index: false,
                    rule: SimpRule::Global(entry),
                });
            }
        }
        let base = usize::MAX / 2;
        let rows = match expect_null_args(arguments, "optional simp rule list")? {
            [] => &[][..],
            [open, rows, close] => {
                expect_atom(open, "[", "simp rule opener")?;
                expect_atom(close, "]", "simp rule closer")?;
                expect_null_args(rows, "simp rules")?
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let mut star = false;
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                continue;
            }
            let order = base + index;
            let Syntax::Node { kind, args, .. } = row else {
                return Err(error(TacticError::MalformedScript));
            };
            if *kind == parser_kind(&["Tactic", "simpStar"]) {
                if simp_all {
                    return Err(error(TacticError::MalformedScript));
                }
                star = true;
                continue;
            }
            if *kind == parser_kind(&["Tactic", "simpErase"]) {
                let [_, Syntax::Ident { val, .. }] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                let name = self.simp_erasure_name(val)?;
                simulation
                    .candidates
                    .retain(|c| !matches!(&c.origin, Used::Decl { name: n, .. } if *n == name));
                simulation.unfold.retain(|n| *n != name);
                continue;
            }
            let [order_slot, direction, term] = args.as_slice() else {
                return Err(error(TacticError::MalformedScript));
            };
            if !expect_null_args(order_slot, "simp rule phase")?.is_empty() {
                return refuse("a `↓` or `↑` rule");
            }
            let reverse = !expect_null_args(direction, "simp direction")?.is_empty();
            let Syntax::Ident { val, .. } = term else {
                return refuse("a rule that is a term, not a name");
            };
            if let Some(local) = self.txn.lctx.find_by_user_name(val).cloned() {
                if local.value.is_some() {
                    if reverse {
                        return refuse("a reversed let variable");
                    }
                    if !simulation.zeta.contains(&local.id) {
                        simulation.zeta.push(local.id.clone());
                    }
                    continue;
                }
                if !self.simulated_proposition(&local.type_)? {
                    return refuse("a local that is not a proposition");
                }
                let Some(text) = printable(val) else {
                    return refuse("a rule name the pin would escape");
                };
                statements.push(self.instantiate(&local.type_)?);
                simulation.candidates.push(Candidate {
                    rule: SimpRule::Explicit(RewriteRule {
                        syntax: term,
                        reverse,
                        global: None,
                    }),
                    origin: Used::Stx(if reverse { format!("← {text}") } else { text }),
                    priority: 1000,
                    order,
                    no_index: true,
                });
                continue;
            }
            let mut head = val.clone();
            while !head.parent().is_anonymous() {
                head = head.parent();
            }
            if self.txn.lctx.find_by_user_name(&head).is_some() {
                return refuse("a field of a local as a rule");
            }
            // `_root_.x` names the global `x` even where a local is spelled `x`.
            let rooted = scope::components(val)
                .is_ok_and(|parts| parts.first().is_some_and(|part| part == "_root_"));
            let global = if rooted {
                self.resolve_source_name(val)?
                    .filter(|name| self.txn.env.contains(name))
            } else {
                self.simp_rule_global(term)?
            };
            let Some(name) = global else {
                return refuse("a rule that names no global declaration");
            };
            match self.txn.env.find(&name).cloned() {
                Some(ConstantInfo::Thm(theorem)) => {
                    statements.push(theorem.base.type_.clone());
                    simulation
                        .candidates
                        .retain(|c| !matches!(&c.origin, Used::Decl { name: n, .. } if *n == name));
                    simulation.candidates.push(Candidate {
                        // Keyed as the pin's discrimination tree keys it, as the simplifier
                        // keys an explicit lemma.
                        rule: SimpRule::Explicit(RewriteRule {
                            syntax: term,
                            reverse,
                            global: Some(name.clone()),
                        }),
                        origin: Used::Decl {
                            name: name.clone(),
                            inv: reverse,
                        },
                        priority: 1000,
                        order,
                        no_index: false,
                    });
                }
                Some(ConstantInfo::Defn(_)) if !reverse => {
                    if !self.simulated_simple_definition(&name)? {
                        return refuse("unfolding a recursive or matching definition by name");
                    }
                    simulation
                        .candidates
                        .retain(|c| !matches!(&c.origin, Used::Decl { name: n, .. } if *n == name));
                    if !simulation.unfold.contains(&name) {
                        simulation.unfold.push(name);
                    }
                }
                _ => return refuse("a rule this model does not read"),
            }
        }
        if star {
            // `applyStarArg`: every propositional hypothesis, after the arguments.
            for (index, local) in self.txn.lctx.decls().to_vec().into_iter().enumerate() {
                self.tick()?;
                if local.value.is_some()
                    || self.is_matrix_hypothesis(&local)
                    || !self.simulated_proposition(&local.type_)?
                {
                    continue;
                }
                statements.push(self.instantiate(&local.type_)?);
                simulation.candidates.push(Candidate {
                    rule: SimpRule::Local(local.id.clone()),
                    origin: Used::Fvar(local.id.clone()),
                    priority: 1000,
                    order: base + rows.len() + index,
                    no_index: true,
                });
            }
        }
        // A default-set definition is refused only where it heads a visited node
        // (`simulated_reduce_step`).
        Ok((simulation, statements))
    }

    /// A definition the pin's `simp [f]` unfolds by delta (`toUnfold`) rather than by
    /// equation theorems: not recursive, no match, no projection, not irreducible.
    fn simulated_simple_definition(&mut self, name: &Name) -> Result<bool, NatDefinitionElabError> {
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(false);
        };
        if definition.safety != DefinitionSafety::Safe || self.simulated_projection(name).is_some()
        {
            return Ok(false);
        }
        let table = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        if table.status(name) == crate::reducibility::Reducibility::Irreducible {
            return Ok(false);
        }
        let mut pending = vec![definition.value.clone()];
        while let Some(term) = pending.pop() {
            self.tick()?;
            if let ExprNode::Const { name: inner, .. } = term.node() {
                if inner == name || self.simulated_eliminator(inner) {
                    return Ok(false);
                }
                if let LeafView::Str(leaf) = inner.leaf_view()
                    && (leaf == "fix" || leaf == "fixF")
                {
                    return Ok(false);
                }
            }
            pending.extend(children(&term).into_iter().flatten().cloned());
        }
        Ok(true)
    }

    /// A matcher, recursor or auxiliary eliminator, which `simpMatch`/`reduceRecMatcher?` reduce.
    fn simulated_eliminator(&self, name: &Name) -> bool {
        if matches!(
            self.txn.env.find(name),
            Some(ConstantInfo::Rec(_) | ConstantInfo::Quot(_))
        ) {
            return true;
        }
        match name.leaf_view() {
            LeafView::Str(leaf) => {
                matches!(
                    leaf,
                    "casesOn" | "recOn" | "brecOn" | "binductionOn" | "below" | "ibelow"
                ) || leaf
                    .strip_prefix("match_")
                    .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
            }
            _ => false,
        }
    }

    /// A projection function's parameter count and whether it projects a class: its value is
    /// `fun params self => self.i`.
    fn simulated_projection(&self, name: &Name) -> Option<(usize, bool)> {
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name) else {
            return None;
        };
        let mut body = &definition.value;
        let mut binders = Vec::new();
        while let ExprNode::Lam {
            body: next,
            binder_info,
            ..
        } = body.node()
        {
            binders.push(*binder_info);
            body = next;
        }
        match body.node() {
            ExprNode::Proj { expr, .. } if matches!(expr.node(), ExprNode::BVar { idx: 0 }) => {
                let last = binders.last()?;
                Some((binders.len() - 1, *last == BinderInfo::InstImplicit))
            }
            _ => None,
        }
    }

    /// One `Simp.main` run (fresh cache, shared `UsedSimps`), with the conditions under which
    /// the pin's zeta-delta tracking adds nothing this model does not see.
    fn simulated_run(
        &mut self,
        simulation: &mut Simulation<'_>,
        goal: &ProofGoal,
        expr: &Expr,
        statements: &[Expr],
    ) -> Result<Expr, NatDefinitionElabError> {
        // A let variable outside the call's set, in the term or a rule: the pin's unifier
        // never unfolds it (`zetaDelta := false`), which this engine's need not follow.
        let mentioned = |expr: &Expr, found: &mut Vec<FVarId>| {
            let mut pending = vec![expr.clone()];
            while let Some(term) = pending.pop() {
                if let ExprNode::FVar { id } = term.node()
                    && !found.contains(id)
                {
                    found.push(id.clone());
                }
                pending.extend(children(&term).into_iter().flatten().cloned());
            }
        };
        let mut direct = Vec::new();
        mentioned(expr, &mut direct);
        for statement in statements {
            mentioned(statement, &mut direct);
        }
        for id in &direct {
            self.tick()?;
            if goal
                .lctx
                .find(id)
                .is_some_and(|local| local.value.is_some())
                && !simulation.zeta.contains(id)
            {
                return refuse("a let variable that the call does not name");
            }
        }
        simulation.cache.clear();
        let result = self.simulated_simp(simulation, expr)?;
        // `updateUsedSimpsWithZetaDelta`: a named let variable the pin's unifier or type
        // inference unfolded is recorded at the end of the run. The model sees only the
        // traversal's; one that the run's terms reach otherwise stops it.
        let mut reach = direct.clone();
        let mut index = 0;
        while index < reach.len() {
            self.tick()?;
            if let Some(value) = goal
                .lctx
                .find(&reach[index])
                .and_then(|local| local.value.clone())
            {
                mentioned(&value, &mut reach);
            }
            index += 1;
        }
        // The tracked set is added in the set's own order, which the model does not know
        // past one entry.
        let pending: Vec<FVarId> = simulation
            .tracked
            .iter()
            .filter(|id| !simulation.used.contains(&Used::Fvar((*id).clone())))
            .cloned()
            .collect();
        if pending.len() > 1 {
            return refuse("two named let variables the pin's unifier unfolded");
        }
        for id in pending {
            simulation.record(Used::Fvar(id));
        }
        simulation.tracked.clear();
        for id in &simulation.zeta {
            if !simulation.used.contains(&Used::Fvar(id.clone()))
                && reach.contains(id)
                && !direct.contains(id)
            {
                return refuse("a named let variable reached only through another's value");
            }
        }
        Ok(result)
    }

    /// `simp` (`simpImpl` and `simpLoop`).
    fn simulated_simp(
        &mut self,
        simulation: &mut Simulation<'_>,
        expr: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        if let Some(result) = simulation.cache.get(expr) {
            return Ok(result.clone());
        }
        simulation.steps += 1;
        if simulation.steps > MAX_SIMULATION_STEPS {
            return refuse("a simplification longer than this model follows");
        }
        // The model recurses on the native stack, a few frames per level.
        if simulation.nesting >= MAX_SIMULATION_NESTING {
            return refuse("a term nested deeper than this model follows");
        }
        simulation.nesting += 1;
        let result = self.simulated_simp_at(simulation, expr);
        simulation.nesting -= 1;
        result
    }

    fn simulated_simp_at(
        &mut self,
        simulation: &mut Simulation<'_>,
        expr: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        if expr.has_expr_mvar() || expr.has_level_mvar() || expr.has_loose_bvars() {
            return refuse("an open term");
        }
        self.simulated_pre(expr)?;
        if let Some(next) = self.simulated_reduce_step(simulation, expr)? {
            let result = self.simulated_simp(simulation, &next)?;
            simulation.cache.insert(expr.clone(), result.clone());
            return Ok(result);
        }
        let stepped = self.simulated_step(simulation, expr)?;
        let (result, done) = match self.simulated_rewrite(simulation, &stepped)? {
            Some(next) => (next, false),
            None => match self.simulated_post_procedures(simulation, &stepped)? {
                Some(next) => (next, true),
                None => (stepped, false),
            },
        };
        let result = if !done && result != *expr {
            self.simulated_simp(simulation, &result)?
        } else {
            result
        };
        simulation.cache.insert(expr.clone(), result.clone());
        Ok(result)
    }

    /// `pre`: no pre theorem is in the fragment; a pre procedure's head or a matcher stops it.
    fn simulated_pre(&mut self, expr: &Expr) -> Result<(), NatDefinitionElabError> {
        let Some(name) = head_name(expr) else {
            return Ok(());
        };
        if in_list(name, PRE_HEADS) {
            return refuse("`ite`, `dite` or another head of a pre simplification procedure");
        }
        if self.simulated_eliminator(name) {
            return refuse("a match or recursor application");
        }
        Ok(())
    }

    /// `reduceStep` (`Main.lean:213-245`): only literal folding and unfolding by name are
    /// in the fragment.
    fn simulated_reduce_step(
        &mut self,
        simulation: &mut Simulation<'_>,
        expr: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if let ExprNode::Lit {
            literal: Literal::Nat(n),
        } = expr.node()
        {
            if simulation.unfold.contains(&named("OfNat.ofNat")) {
                return refuse("unfolding `OfNat.ofNat`");
            }
            let Some(value) = n.to_u64() else {
                return refuse("a large literal");
            };
            return Ok(Some(nat_literal(value)));
        }
        let (head, args) = spine(expr);
        match head.node() {
            ExprNode::Lam { .. } if !args.is_empty() => refuse("a beta redex"),
            ExprNode::LetE { .. } => refuse("a `let` term"),
            ExprNode::Proj { .. } => refuse("a projection"),
            ExprNode::MData { .. } => refuse("annotated terms"),
            ExprNode::Const { name, levels } => {
                if let Some((params, class)) = self.simulated_projection(name) {
                    if class && simulation.unfold.contains(name) {
                        return refuse("unfolding a class projection");
                    }
                    if args.len() > params {
                        let major = args[params];
                        let constructor = head_name(major).is_some_and(|major| {
                            matches!(self.txn.env.find(major), Some(ConstantInfo::Ctor(_)))
                        });
                        let local = matches!(major.node(), ExprNode::FVar { id }
                            if self.txn.lctx.find(id).is_some_and(|l| l.value.is_some()));
                        if constructor || local || matches!(major.node(), ExprNode::Lit { .. }) {
                            return refuse("a projection of a constructor");
                        }
                    }
                    return Ok(None);
                }
                if !simulation.unfold.contains(name) {
                    return Ok(None);
                }
                if !self.simulated_simple_definition(name)? {
                    return refuse("unfolding a definition this model does not reduce");
                }
                let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
                    return Ok(None);
                };
                // Issue #2042: a partial application does not unfold.
                let mut lambdas = 0;
                let mut body = &definition.value;
                while let ExprNode::Lam { body: next, .. } = body.node() {
                    lambdas += 1;
                    body = next;
                }
                if lambdas > args.len() {
                    return Ok(None);
                }
                if definition.base.level_params.len() != levels.len() {
                    return refuse("a definition at the wrong universe arity");
                }
                let mut value = self.instantiate_params(
                    &definition.value,
                    &definition.base.level_params,
                    levels,
                )?;
                let mut rest = args.into_iter();
                while let ExprNode::Lam { body, .. } = value.node() {
                    let Some(arg) = rest.next() else {
                        break;
                    };
                    let body = body.clone();
                    value = self.substitute(&body, arg)?;
                }
                for arg in rest {
                    value = Expr::app(value, arg.clone());
                }
                simulation.record(Used::Decl {
                    name: name.clone(),
                    inv: false,
                });
                Ok(Some(value))
            }
            _ => Ok(None),
        }
    }

    /// `simpStep`: congruence over an application's arguments, then its function (`congr`,
    /// `tryAutoCongrTheorem?`, `visitFn`); a local let variable the call names unfolds
    /// (`reduceFVar`); a non-dependent arrow simplifies both sides (`simpArrow`).
    fn simulated_step(
        &mut self,
        simulation: &mut Simulation<'_>,
        expr: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        match expr.node() {
            ExprNode::App { .. } => {
                let (head, args) = spine(expr);
                if let Some(name) = head_name(head) {
                    // `isOfNatNatLit`, `isOfScientificLit`, `isCharLit`: not visited.
                    if (*name == named("OfNat.ofNat")
                        && args.len() >= 3
                        && matches!(args[1].node(), ExprNode::Lit { .. }))
                        || (*name == named("OfScientific.ofScientific") && args.len() == 5)
                        || (*name == named("Char.ofNat") && args.len() == 1)
                    {
                        return Ok(expr.clone());
                    }
                    if in_list(name, CONGRUENCE_HEADS) {
                        return refuse("a head with a congruence theorem");
                    }
                    if let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name)
                        && self.simulated_class(&constructor.induct)
                    {
                        return refuse("a class constructor");
                    }
                } else if !matches!(head.node(), ExprNode::FVar { .. }) {
                    return refuse("an application whose head is not a constant or a local");
                }
                let (automatic, kinds, dependents) = self.simulated_congruence(head, &args)?;
                // `simpAppUsingCongr` visits the function first; `tryAutoCongrTheorem?` then
                // `visitFn`, last.
                let mut rebuilt = if automatic {
                    head.clone()
                } else {
                    self.simulated_simp(simulation, head)?
                };
                let mut fresh = Vec::new();
                for (arg, kind) in args.iter().zip(kinds) {
                    let next = match kind {
                        ArgKind::Eq => self.simulated_simp(simulation, arg)?,
                        ArgKind::Fixed => {
                            self.simulated_inert(simulation, arg)?;
                            (*arg).clone()
                        }
                        ArgKind::Keep => (*arg).clone(),
                    };
                    fresh.push(next);
                }
                // A cast or subsingleton instance over a rewritten argument is transported.
                for (_, rewritten) in dependents {
                    if fresh[rewritten] != *args[rewritten] {
                        return refuse("a rewritten argument that a proof or instance depends on");
                    }
                }
                if automatic {
                    rebuilt = self.simulated_simp(simulation, head)?;
                }
                for arg in fresh {
                    rebuilt = Expr::app(rebuilt, arg);
                }
                Ok(rebuilt)
            }
            ExprNode::FVar { id } => {
                if simulation.zeta.contains(id) {
                    let local = self
                        .txn
                        .lctx
                        .find(id)
                        .cloned()
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    let value = local
                        .value
                        .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                    simulation.record(Used::Fvar(id.clone()));
                    return self.instantiate(&value);
                }
                Ok(expr.clone())
            }
            ExprNode::Const { .. } | ExprNode::Sort { .. } | ExprNode::Lit { .. } => {
                Ok(expr.clone())
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } if !body.has_loose_bvars() => {
                // `simp_all`'s contextual arrow adds its antecedent as a theorem.
                if simulation.contextual {
                    return refuse("an implication under `simp_all`");
                }
                let domain = self.simulated_simp(simulation, binder_type)?;
                let body = self.simulated_simp(simulation, body)?;
                Ok(Expr::forall_e(
                    binder_name.clone(),
                    domain,
                    body,
                    *binder_info,
                ))
            }
            _ => refuse("a binder, `let`, projection or annotation"),
        }
    }

    /// Whether `name` is a class; an unreadable registry counts as one, which only stops the
    /// model.
    fn simulated_class(&self, name: &Name) -> bool {
        self.registry_cache
            .read(&self.txn.env)
            .map(|registry| registry.is_class(name))
            .unwrap_or(true)
    }

    /// How the pin's `congr` visits `head` applied to `args`: by the automatic congruence
    /// theorem (`mkCongrSimp?`, only for a full application whose `getCongrSimpKinds` has a
    /// cast or a subsingleton instance), else by `simpAppUsingCongr`; each argument's role;
    /// and the (cast or instance, rewritten argument) pairs the automatic theorem transports.
    #[allow(clippy::type_complexity)]
    fn simulated_congruence(
        &mut self,
        head: &Expr,
        args: &[&Expr],
    ) -> Result<(bool, Vec<ArgKind>, Vec<(usize, usize)>), NatDefinitionElabError> {
        let (binders, mut rest) = self.simulated_binders(head, args.len())?;
        if !matches!(rest.node(), ExprNode::ForallE { .. }) && !rest.has_loose_bvars() {
            rest = self.whnf(&rest)?;
        }
        let full = !matches!(rest.node(), ExprNode::ForallE { .. });
        let n = args.len();
        // Binder `j`'s domain sits under `j` binders: binder `i` is its bvar `j - 1 - i`.
        let depends = |domain: &Expr, depth: usize, i: usize| {
            let index = (depth - 1 - i) as u32;
            domain.has_loose_bvar(index)
        };
        let body = |mut domain: &Expr| {
            while let ExprNode::ForallE { body, .. } = domain.node() {
                domain = body;
            }
            head_name(domain).cloned()
        };
        let mut instance = Vec::with_capacity(n);
        let mut proof = Vec::with_capacity(n);
        let mut decidable = Vec::with_capacity(n);
        for (i, arg) in args.iter().enumerate() {
            self.tick()?;
            let class = body(&binders[i].0);
            instance.push(
                binders[i].1 != BinderInfo::Default
                    && class
                        .as_ref()
                        .is_some_and(|class| self.simulated_class(class)),
            );
            decidable.push(class.is_some_and(|class| class == named("Decidable")));
            proof.push(match self.known_type(arg)? {
                Some(arg_type) => self.simulated_proposition(&arg_type)?,
                None => return refuse("an argument whose type is unknown"),
            });
        }
        let back = |j: usize, i: usize| depends(&binders[j].0, j, i);
        let forward = |i: usize| (i + 1..n).any(|j| back(j, i)) || depends(&rest, n, i);
        if full {
            // `getCongrSimpKinds`, `fixKindsForDependencies`.
            #[derive(Clone, Copy, PartialEq)]
            enum Kind {
                Fixed,
                Cast,
                Subsingleton,
                Eq,
            }
            let mut kinds: Vec<Kind> = Vec::with_capacity(n);
            for i in 0..n {
                kinds.push(if depends(&rest, n, i) {
                    Kind::Fixed
                } else if proof[i] {
                    Kind::Cast
                } else if instance[i] {
                    if decidable[i] && (0..i).any(|j| back(i, j) && kinds[j] == Kind::Eq) {
                        Kind::Subsingleton
                    } else {
                        Kind::Fixed
                    }
                } else {
                    Kind::Eq
                });
            }
            for i in 0..n {
                for j in i + 1..n {
                    if back(j, i) && matches!(kinds[j], Kind::Eq | Kind::Fixed) {
                        kinds[i] = Kind::Fixed;
                        break;
                    }
                }
            }
            if kinds
                .iter()
                .any(|kind| matches!(kind, Kind::Cast | Kind::Subsingleton))
            {
                let mut dependents = Vec::new();
                for (j, kind) in kinds.iter().enumerate() {
                    if matches!(kind, Kind::Cast | Kind::Subsingleton) {
                        for (i, earlier) in kinds.iter().enumerate().take(j) {
                            if *earlier == Kind::Eq && back(j, i) {
                                dependents.push((j, i));
                            }
                        }
                    }
                }
                let roles = kinds
                    .iter()
                    .map(|kind| match kind {
                        Kind::Eq => ArgKind::Eq,
                        Kind::Fixed => ArgKind::Fixed,
                        Kind::Cast | Kind::Subsingleton => ArgKind::Keep,
                    })
                    .collect();
                return Ok((true, roles, dependents));
            }
        }
        // `simpAppUsingCongr`: an instance is not visited (`Simp.Config.instances := false`), a
        // proof is returned unchanged (`simpImpl`'s `isProof`), an argument without forward
        // dependencies is simplified, another is left to `dsimp`.
        let roles = (0..n)
            .map(|i| {
                if instance[i] || proof[i] {
                    ArgKind::Keep
                } else if !forward(i) {
                    ArgKind::Eq
                } else {
                    ArgKind::Fixed
                }
            })
            .collect();
        Ok((false, roles, Vec::new()))
    }

    /// The first `count` binders of `head`'s type, each domain under the binders before it,
    /// and the rest of the type (`forallTelescopeReducing`, here only where the type to reduce
    /// mentions no earlier binder).
    #[allow(clippy::type_complexity)]
    fn simulated_binders(
        &mut self,
        head: &Expr,
        count: usize,
    ) -> Result<(Vec<(Expr, BinderInfo)>, Expr), NatDefinitionElabError> {
        let Some(type_) = self.known_type(head)? else {
            return refuse("a function whose type is unknown");
        };
        let mut type_ = self.instantiate(&type_)?;
        let mut binders = Vec::new();
        while binders.len() < count {
            self.tick()?;
            if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                if type_.has_loose_bvars() {
                    return refuse("an application beyond its function's dependent arity");
                }
                type_ = self.whnf(&type_)?;
            }
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = type_.node()
            else {
                return refuse("an application beyond its function's arity");
            };
            binders.push((binder_type.clone(), *binder_info));
            type_ = body.clone();
        }
        Ok((binders, type_))
    }

    /// A fixed argument `dsimp` leaves as it is: types, constants, locals the call does not
    /// unfold and numerals, applied to such.
    fn simulated_inert(
        &mut self,
        simulation: &Simulation<'_>,
        expr: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        let (head, args) = spine(expr);
        if nat_value(expr).is_some() && !matches!(expr.node(), ExprNode::Lit { .. }) {
            return Ok(());
        }
        let fine = match head.node() {
            ExprNode::Sort { .. } => args.is_empty(),
            ExprNode::Const { name, .. } => {
                // A type former, an instance, or a class projection of one, none of which a
                // default `rfl` theorem or `dsimproc` rewrites; a projection reduces only of a
                // constructor (`reduceProjFn?`).
                let former = matches!(self.txn.env.find(name), Some(ConstantInfo::Induct(_)));
                let instance = self
                    .registry_cache
                    .read(&self.txn.env)
                    .is_ok_and(|registry| registry.is_instance(name));
                let projection = match self.simulated_projection(name) {
                    None => false,
                    Some((params, class)) => {
                        class
                            && args.get(params).is_some_and(|major| {
                                !head_name(major).is_some_and(|major| {
                                    matches!(self.txn.env.find(major), Some(ConstantInfo::Ctor(_)))
                                }) && !matches!(major.node(), ExprNode::Lit { .. })
                            })
                    }
                };
                (former || instance || projection) && !simulation.unfold.contains(name)
            }
            ExprNode::FVar { id } => {
                !simulation.zeta.contains(id)
                    && self.txn.lctx.find(id).is_some_and(|l| l.value.is_none())
            }
            _ => false,
        };
        if !fine {
            return refuse("an argument this model does not know `dsimp` leaves alone");
        }
        for arg in args {
            self.simulated_inert(simulation, arg)?;
        }
        Ok(())
    }

    /// `rewritePost` (`rewrite?`): the candidates that unify at `expr` and whose premises
    /// discharge, the first by priority and discrimination-tree order; it records the
    /// premises' rules, then itself.
    fn simulated_rewrite(
        &mut self,
        simulation: &mut Simulation<'_>,
        expr: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        // A let variable heads the pin's `.fvar` key: `zetaDelta := false` leaves one outside the
        // call's set alone, and one in it was already unfolded (`reduceFVar`). So only a rule
        // the pin keys as a star is retrieved there, as at any other local.
        let index = match spine(expr).0.node() {
            ExprNode::FVar { id } if self.txn.lctx.find(id).is_some_and(|l| l.value.is_some()) => {
                let table = crate::reducibility::table(&self.txn.env).map_err(|error| {
                    failure(SourceInferenceError::Unification(Box::new(
                        UnificationError::Reducibility(error),
                    )))
                })?;
                Some(SimpTargetIndex {
                    applications: HashMap::new(),
                    environment: simp_key_environment(&self.txn.env),
                    table,
                })
            }
            _ => self.simp_root_index(expr)?,
        };
        let saved = simulation.used.clone();
        // (candidate, result, `UsedSimps` after its discharge)
        let mut found: Vec<(usize, Expr, Vec<Used>)> = Vec::new();
        for position in 0..simulation.candidates.len() {
            // As the simplifier's own loop, a rule the key filter rejects charges nothing: the
            // default set is thousands of rules at every node.
            let skipped = {
                let candidate = &simulation.candidates[position];
                matches!((&candidate.rule, &simulation.excluded),
                    (SimpRule::Local(id), Some(excluded)) if id == excluded)
                    || !self.simp_rule_admitted(
                        &candidate.rule,
                        index.as_ref(),
                        SimpKeySide::Rewrite,
                    )
            };
            if skipped {
                continue;
            }
            self.tick()?;
            let candidate = simulation.candidates[position].clone();
            let Some((result, premises, perm, pattern)) = self.simulated_match(&candidate, expr)?
            else {
                continue;
            };
            // A named let variable the rule mentions and the term does not: the pin's unifier
            // unfolded it, and its zeta-delta tracking keeps that past the attempt.
            for id in simulation.zeta.clone() {
                if mentions(&pattern, &id) {
                    if mentions(expr, &id) {
                        return refuse("a named let variable on both sides of a match");
                    }
                    if !simulation.tracked.contains(&id) {
                        simulation.tracked.push(id);
                    }
                }
            }
            if result == *expr {
                // The pin discharges before it finds the rewrite changes nothing.
                if !premises.is_empty() {
                    return refuse("a conditional rule that changes nothing");
                }
                continue;
            }
            // `tryTheoremCore` discharges first, then rejects a permutation rewrite that does not
            // decrease in the pin's term order (`Rewrite.lean:143-150`); a rejected candidate
            // records nothing. Uses its discharge recorded before that rejection stay recorded
            // at the pin, which this model does not reproduce.
            if perm {
                if !premises.is_empty() {
                    return refuse("a conditional permutation rule");
                }
                if !self.simp_ac_lt(&result, expr)? {
                    continue;
                }
            }
            let mut discharged = true;
            for premise in &premises {
                if !self.simulated_discharge(simulation, premise)? {
                    discharged = false;
                    break;
                }
            }
            if discharged {
                found.push((position, result, simulation.used.clone()));
            }
            simulation.used = saved.clone();
        }
        if found.is_empty() {
            return Ok(None);
        }
        let top = found
            .iter()
            .map(|(position, ..)| simulation.candidates[*position].priority)
            .max()
            .expect("a candidate was found");
        found.retain(|(position, ..)| simulation.candidates[*position].priority == top);
        let mut winner = 0;
        for other in 1..found.len() {
            let first =
                self.simulated_precedes(simulation, found[other].0, found[winner].0, expr)?;
            if first {
                winner = other;
            }
        }
        let (position, result, used) = found.swap_remove(winner);
        simulation.used = used;
        let origin = simulation.candidates[position].origin.clone();
        simulation.record(self.simulated_equation_origin(origin));
        Ok(Some(result))
    }

    /// `recordSimpTheorem`: an equation theorem `f.eq_n` records `f`.
    fn simulated_equation_origin(&self, origin: Used) -> Used {
        if let Used::Decl { name, inv: false } = &origin
            && let LeafView::Str(leaf) = name.leaf_view()
            && (leaf == "eq_def"
                || leaf
                    .strip_prefix("eq_")
                    .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit())))
            && matches!(
                self.txn.env.find(&name.parent()),
                Some(ConstantInfo::Defn(_))
            )
        {
            return Used::Decl {
                name: name.parent(),
                inv: false,
            };
        }
        origin
    }

    /// Unify `candidate` at `expr`: its result, its open premises, and whether it is a
    /// permutation rule.
    #[allow(clippy::type_complexity)]
    fn simulated_match(
        &mut self,
        candidate: &Candidate<'_>,
        expr: &Expr,
    ) -> Result<Option<(Expr, Vec<Expr>, bool, Expr)>, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let attempt = (|| {
            let term = trial.selected_simp_term(&candidate.rule)?;
            let reverse = candidate.rule.reverse();
            let Some(found) = trial.instantiate_simp_rule_at_root(term, expr, reverse)? else {
                return Ok(None);
            };
            let perm = found.perm;
            let Some((_, _, from, to)) = equality_target(&found.rule.type_) else {
                return refuse("a rule that is not an equation after its preparation");
            };
            let result = trial.instantiate(if reverse { &from } else { &to })?;
            let pattern = trial.instantiate(if reverse { &to } else { &from })?;
            let mut premises = Vec::new();
            for premise in &found.premises {
                premises.push(trial.instantiate(&premise.target)?);
            }
            if result.has_expr_mvar() || result.has_level_mvar() {
                return refuse("a rule whose result is left open");
            }
            Ok(Some((result, premises, perm, pattern)))
        })();
        self.charge_rewrite_trial(&trial);
        match attempt {
            Ok(found) => Ok(found),
            Err(error) if Self::rewrite_nonmatch(&error) => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// A rule's pattern and the side it rewrites to, under its binders (pattern variables are
    /// loose bound variables), as `mkSimpTheoremKeys` reads the preprocessed statement.
    fn simulated_pattern(
        &mut self,
        statement: &Expr,
        reverse: bool,
    ) -> Result<(Expr, Option<Expr>), NatDefinitionElabError> {
        let mut body = statement;
        while let ExprNode::ForallE { body: next, .. } = body.node() {
            body = next;
        }
        let (head, args) = spine(body);
        let Some(name) = head_name(head) else {
            return Ok((body.clone(), None));
        };
        let text = name.to_display_string();
        Ok(match (text.as_str(), args.len()) {
            ("Eq", 3) | ("Iff", 2) => {
                let (left, right) = if text == "Eq" {
                    (args[1].clone(), args[2].clone())
                } else {
                    (args[0].clone(), args[1].clone())
                };
                if reverse {
                    (right, Some(left))
                } else {
                    (left, Some(right))
                }
            }
            // `preprocess`: `¬ p` rewrites `p` to `False`, `a ≠ b` rewrites `a = b`; with `true`
            // or `false` on the right they become other equations.
            ("Not", 1) | ("Ne", 3) => {
                let (inner, inner_args) = spine(args[0]);
                let boolean =
                    |side: &Expr| is_const(side, "Bool.true") || is_const(side, "Bool.false");
                if (text == "Ne" && boolean(args[2]))
                    || (is_const(inner, "Eq") && inner_args.len() == 3 && boolean(inner_args[2]))
                {
                    return refuse("a refutation of a `Bool` equation");
                }
                if text == "Ne" {
                    let ExprNode::Const { levels, .. } = head.node() else {
                        return Err(error(TacticError::MalformedScript));
                    };
                    let equation = app(
                        Expr::const_(named("Eq"), levels.clone()),
                        [args[0].clone(), args[1].clone(), args[2].clone()],
                    );
                    (equation, None)
                } else {
                    (args[0].clone(), None)
                }
            }
            _ => (body.clone(), None),
        })
    }

    /// Whether candidate `a` comes before `b` in the pin's discrimination-tree order at `expr`
    /// (`getMatchLoop` visits the `*` edge first; one leaf keeps insertion order).
    fn simulated_precedes(
        &mut self,
        simulation: &Simulation<'_>,
        a: usize,
        b: usize,
        expr: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let first = self.simulated_key_path(&simulation.candidates[a], expr)?;
        let second = self.simulated_key_path(&simulation.candidates[b], expr)?;
        for (x, y) in first.iter().zip(&second) {
            if x == y {
                continue;
            }
            return match (x, y) {
                (Key::Star, _) => Ok(true),
                (_, Key::Star) => Ok(false),
                _ => refuse("two rules whose order this model cannot place"),
            };
        }
        if first.len() != second.len() {
            return refuse("two rules whose order this model cannot place");
        }
        let (x, y) = (
            &simulation.candidates[a].order,
            &simulation.candidates[b].order,
        );
        if x == y {
            return refuse("two rules at one place");
        }
        Ok(x < y)
    }

    /// The pin's `DiscrTree.mkPath` of a candidate's pattern (`DiscrTree/Main.lean:262-342`),
    /// read alongside its instance at `expr` for the arguments' types.
    fn simulated_key_path(
        &mut self,
        candidate: &Candidate<'_>,
        expr: &Expr,
    ) -> Result<Vec<Key>, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let result = (|| {
            let term = trial.selected_simp_term(&candidate.rule)?;
            let statement = trial.instantiate(&term.type_)?;
            let (pattern, _) = trial.simulated_pattern(&statement, candidate.rule.reverse())?;
            let mut keys = Vec::new();
            let mut pending = vec![(pattern, expr.clone(), true)];
            while let Some((pattern, instance, root)) = pending.pop() {
                trial.tick()?;
                if matches!(pattern.node(), ExprNode::BVar { .. }) {
                    keys.push(Key::Star);
                    continue;
                }
                let (head, args) = spine(&pattern);
                let (instance_head, instance_args) = spine(&instance);
                let reducible = |trial: &Context,
                                 name: &Name|
                 -> Result<bool, NatDefinitionElabError> {
                    let table = crate::reducibility::table(&trial.txn.env).map_err(|error| {
                        failure(SourceInferenceError::Unification(Box::new(
                            UnificationError::Reducibility(error),
                        )))
                    })?;
                    Ok(table.status(name) == crate::reducibility::Reducibility::Reducible)
                };
                let key = match head.node() {
                    ExprNode::BVar { .. } => {
                        keys.push(Key::Star);
                        continue;
                    }
                    ExprNode::Lit { literal } => {
                        keys.push(Key::Lit(literal.clone()));
                        continue;
                    }
                    ExprNode::Const { name, .. } => {
                        if reducible(&trial, name)? {
                            return refuse(
                                "a rule whose pattern unfolds at reducible transparency",
                            );
                        }
                        if !root {
                            if let Some(value) = key_numeral(&pattern) {
                                keys.push(Key::Lit(Literal::Nat(
                                    fln_core::expr::NatLit::from_u64(value),
                                )));
                                continue;
                            }
                            if key_offset(&pattern) {
                                keys.push(Key::Star);
                                continue;
                            }
                        }
                        Key::Const(name.clone(), args.len())
                    }
                    ExprNode::FVar { id } => Key::FVar(id.clone(), args.len()),
                    ExprNode::ForallE { binder_type, .. } if args.is_empty() => {
                        keys.push(Key::Arrow);
                        let ExprNode::ForallE {
                            binder_type: instance_domain,
                            ..
                        } = instance.node()
                        else {
                            return refuse("a rule whose instance is not an arrow");
                        };
                        pending.push((binder_type.clone(), instance_domain.clone(), false));
                        continue;
                    }
                    _ => {
                        keys.push(Key::Other);
                        continue;
                    }
                };
                if instance_args.len() != args.len()
                    || std::mem::discriminant(instance_head.node())
                        != std::mem::discriminant(head.node())
                {
                    return refuse("a rule whose instance this model cannot align");
                }
                keys.push(key);
                let infos: Vec<BinderInfo> = trial
                    .simulated_binders(head, args.len())?
                    .0
                    .into_iter()
                    .map(|(_, info)| info)
                    .collect();
                let mut next = Vec::new();
                for (i, (arg, instance_arg)) in args.iter().zip(&instance_args).enumerate() {
                    let ignored = if candidate.no_index {
                        true
                    } else {
                        match infos.get(i) {
                            Some(BinderInfo::InstImplicit) => true,
                            Some(BinderInfo::Implicit | BinderInfo::StrictImplicit) => {
                                // `!isType a`.
                                match trial.known_type(instance_arg)? {
                                    Some(type_) => {
                                        let type_ = trial.whnf(&type_)?;
                                        !matches!(type_.node(), ExprNode::Sort { .. })
                                    }
                                    None => return refuse("an argument whose type is unknown"),
                                }
                            }
                            _ => match trial.known_type(instance_arg)? {
                                Some(type_) => trial.simulated_proposition(&type_)?,
                                None => return refuse("an argument whose type is unknown"),
                            },
                        }
                    };
                    if ignored {
                        next.push(None);
                    } else {
                        next.push(Some(((*arg).clone(), (*instance_arg).clone())));
                    }
                }
                // Depth first, left to right: push in reverse.
                for item in next.into_iter().rev() {
                    match item {
                        None => {
                            pending.push((Expr::bvar(0).expect("zero index"), expr.clone(), false))
                        }
                        Some((arg, instance_arg)) => pending.push((arg, instance_arg, false)),
                    }
                }
            }
            Ok(keys)
        })();
        self.charge_rewrite_trial(&trial);
        result
    }

    /// `dischargeDefault?`: simplify the premise to `True`, the cache restored after it and
    /// `UsedSimps` restored on failure (`discharge?'`, `Rewrite.lean:32-58`).
    fn simulated_discharge(
        &mut self,
        simulation: &mut Simulation<'_>,
        premise: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if simulation.depth >= MAX_DISCHARGE_DEPTH {
            return Ok(false);
        }
        // `isEqnThmHypothesis`: `∀ …, s = t → … → False`.
        if let ExprNode::ForallE { .. } = premise.node() {
            let mut body = premise;
            while let ExprNode::ForallE { body: next, .. } = body.node() {
                body = next;
            }
            if is_const(body, "False") {
                return refuse("an equation-theorem hypothesis");
            }
        }
        let used = simulation.used.clone();
        let cache = simulation.cache.clone();
        simulation.depth += 1;
        let result = self.simulated_simp(simulation, premise);
        simulation.depth -= 1;
        simulation.cache = cache;
        let result = result?;
        if is_const(&result, "True") {
            return Ok(true);
        }
        if equality_target(&result).is_some_and(|(_, _, left, right)| {
            matches!(spine(&left).0.node(), ExprNode::MVar { .. })
                || matches!(spine(&right).0.node(), ExprNode::MVar { .. })
        }) {
            return refuse("a premise `dischargeRfl` would close");
        }
        simulation.used = used;
        Ok(false)
    }

    /// The default post simplification procedures (`userPostSimprocs`): the `Nat` literal
    /// operators are evaluated as `Nat.reduceBin` does; every other procedure that may fire at
    /// `expr` stops the model.
    fn simulated_post_procedures(
        &mut self,
        simulation: &mut Simulation<'_>,
        expr: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (head, args) = spine(expr);
        let Some(name) = head_name(head) else {
            return Ok(None);
        };
        let text = name.to_display_string();
        let stop = |reason| refuse::<Option<Expr>>(reason);
        if in_list(name, SIMPROC_HEADS) {
            return stop("a head with a simplification procedure");
        }
        // `Nat` relations between numerals: `Nat.reduceEqDiff`, `Nat.reduceLeDiff`,
        // `Nat.reduceLT`, `Nat.reduceGT` (`evalPropStep`, `.done`), `Nat.reduceBEq`,
        // `Nat.reduceBNe` (`reduceBoolPred`), each the one the pin's order runs first, measured.
        if let Some((procedure, value)) = Self::simulated_nat_relation(&text, &args) {
            simulation.record(Used::Simproc(named(procedure)));
            let boolean = matches!(procedure, "Nat.reduceBEq" | "Nat.reduceBNe");
            let result = match (boolean, value) {
                (false, true) => "True",
                (false, false) => "False",
                (true, true) => "Bool.true",
                (true, false) => "Bool.false",
            };
            return Ok(Some(Expr::const_(named(result), Vec::new())));
        }
        match (text.as_str(), args.len()) {
            ("Eq", 3) => {
                let (type_, left, right) = (args[0], args[1], args[2]);
                let constructor = |side: &Expr| {
                    literal_like(side)
                        || head_name(side).is_some_and(|name| {
                            matches!(self.txn.env.find(name), Some(ConstantInfo::Ctor(_)))
                        })
                };
                if constructor(left) && constructor(right) {
                    return stop("an equation between constructors or literals");
                }
                if is_const(type_, "Nat")
                    && nat_offset_or_literal(left)
                    && nat_offset_or_literal(right)
                {
                    return stop("a `Nat` equation `Nat.reduceEqDiff` reads");
                }
                if literal_type(type_) && (literal_like(left) || literal_like(right)) {
                    return stop("an equation of literals");
                }
                Ok(None)
            }
            ("Not", 1) => {
                let (inner, inner_args) = spine(args[0]);
                if is_const(inner, "Eq")
                    && inner_args.len() == 3
                    && literal_type(inner_args[0])
                    && (literal_like(inner_args[1]) || literal_like(inner_args[2]))
                {
                    return stop("a disequation of literals");
                }
                Ok(None)
            }
            (_, 4) if in_list(name, RELATION_HEADS) => {
                let (type_, left, right) = (args[0], args[2], args[3]);
                // `Nat.reduceLeDiff`, `Nat.reduceBeqDiff`, `Nat.reduceBneDiff` read two offsets
                // or numerals (`NatOffset.fromExpr?`); `Nat.reduceLT`/`GT` only numerals.
                if is_const(type_, "Nat") {
                    if matches!(text.as_str(), "LE.le" | "BEq.beq" | "bne")
                        && nat_offset_or_literal(left)
                        && nat_offset_or_literal(right)
                    {
                        return stop("a `Nat` comparison of offsets");
                    }
                    return Ok(None);
                }
                if literal_type(type_) && (literal_like(left) || literal_like(right)) {
                    return stop("a comparison of literals");
                }
                Ok(None)
            }
            (_, 6) if in_list(name, ARITHMETIC_HEADS) => {
                let (left, right) = (args[4], args[5]);
                let nat = args[..3].iter().all(|type_| is_const(type_, "Nat"));
                if nat {
                    if let (Some(a), Some(b)) = (nat_value(left), nat_value(right)) {
                        let Some((_, procedure)) = NAT_BINARY.iter().find(|(op, _)| text == *op)
                        else {
                            return stop("a `Nat` literal operation this model does not evaluate");
                        };
                        let value = match text.as_str() {
                            "HAdd.hAdd" => a.checked_add(b),
                            "HMul.hMul" => a.checked_mul(b),
                            "HSub.hSub" => Some(a.saturating_sub(b)),
                            // `Nat` division by zero is zero, and its remainder the dividend.
                            "HDiv.hDiv" => Some(a.checked_div(b).unwrap_or(0)),
                            _ => Some(a.checked_rem(b).unwrap_or(a)),
                        };
                        let Some(value) = value else {
                            return stop("a large literal");
                        };
                        simulation.record(Used::Simproc(named(procedure)));
                        return Ok(Some(nat_literal(value)));
                    }
                    if text == "HSub.hSub"
                        && nat_offset_or_literal(left)
                        && nat_offset_or_literal(right)
                    {
                        return stop("a `Nat` subtraction `Nat.reduceSubDiff` reads");
                    }
                    if literal_like(left) && literal_like(right) {
                        return stop("a `Nat` literal operation this model does not evaluate");
                    }
                    return Ok(None);
                }
                if literal_like(left) || literal_like(right) {
                    return stop("an operation on literals");
                }
                Ok(None)
            }
            ("Neg.neg", 3) if literal_like(args[2]) => stop("a negated literal"),
            // `String.reduceAppend`, `BitVec.reduceAppend`.
            ("HAppend.hAppend", 6)
                if args[..3].iter().any(|type_| {
                    head_name(type_).is_some_and(|n| in_list(n, &["String", "BitVec"]))
                }) =>
            {
                stop("an append of strings or bit vectors")
            }
            // `Nat.reduceDvd`, `Int.reduceDvd`.
            ("Dvd.dvd", 4) if literal_like(args[2]) || literal_like(args[3]) => {
                stop("a divisibility of literals")
            }
            ("Nat.succ", 1) if literal_like(args[0]) => stop("`Nat.succ` of a literal"),
            ("OfNat.ofNat", 3) if !is_const(args[0], "Nat") => stop("a numeral outside `Nat`"),
            _ => Ok(None),
        }
    }

    /// A `Nat` relation between two numerals: the procedure that decides it and its value.
    fn simulated_nat_relation(text: &str, args: &[&Expr]) -> Option<(&'static str, bool)> {
        let (procedure, type_, left, right) = match (text, args.len()) {
            ("Eq", 3) => ("Nat.reduceEqDiff", args[0], args[1], args[2]),
            ("LE.le", 4) => ("Nat.reduceLeDiff", args[0], args[2], args[3]),
            ("LT.lt", 4) => ("Nat.reduceLT", args[0], args[2], args[3]),
            ("GT.gt", 4) => ("Nat.reduceGT", args[0], args[2], args[3]),
            ("BEq.beq", 4) => ("Nat.reduceBEq", args[0], args[2], args[3]),
            ("bne", 4) => ("Nat.reduceBNe", args[0], args[2], args[3]),
            _ => return None,
        };
        if !is_const(type_, "Nat") {
            return None;
        }
        let (a, b) = (nat_value(left)?, nat_value(right)?);
        let value = match procedure {
            "Nat.reduceEqDiff" | "Nat.reduceBEq" => a == b,
            "Nat.reduceBNe" => a != b,
            "Nat.reduceLeDiff" => a <= b,
            "Nat.reduceLT" => a < b,
            _ => a > b,
        };
        Some((procedure, value))
    }

    /// `mkSimpOnly` (`Simp.lean:618-669`) and `addSuggestion`'s message: `Try this:`, then
    /// `[apply] ` and the call, the rule list filled at the pin's width.
    fn simulated_message(
        &mut self,
        simulation: &Simulation<'_>,
        goal: &ProofGoal,
        simp_all: bool,
        suffix: &str,
    ) -> Result<String, NatDefinitionElabError> {
        let mut args = Vec::new();
        let mut locals = Some(Vec::new());
        let builtins = [named("eq_self"), named("iff_self")];
        for used in &simulation.used {
            self.tick()?;
            match used {
                Used::Decl { name, inv } => {
                    if !self.txn.env.contains(name) {
                        return refuse("a rule that is not a declaration");
                    }
                    if !*inv && builtins.contains(name) {
                        continue;
                    }
                    let shown = self.simulated_unresolve(name, goal)?;
                    args.push(if *inv { format!("← {shown}") } else { shown });
                }
                Used::Simproc(name) => {
                    args.push(printable(name).ok_or_else(|| {
                        error(TacticError::SimpSuggestionUnsupported(
                            "an unprintable name",
                        ))
                    })?);
                }
                Used::Stx(text) => args.push(text.clone()),
                Used::Fvar(id) => {
                    let Some(local) = goal.lctx.find(id) else {
                        continue;
                    };
                    if simp_all && local.value.is_none() {
                        continue;
                    }
                    let visible = goal
                        .lctx
                        .find_by_user_name(&local.user_name)
                        .is_some_and(|visible| visible.id == *id);
                    match (&mut locals, printable(&local.user_name)) {
                        (Some(names), Some(text))
                            if visible && !local.user_name.has_macro_scopes() =>
                        {
                            names.push(text)
                        }
                        _ => locals = None,
                    }
                }
            }
        }
        match locals {
            Some(names) => args.extend(names),
            None => args.push("*".to_string()),
        }
        let keyword = if simp_all { "simp_all" } else { "simp" };
        let mut lines = vec![format!("  [apply] {keyword} only")];
        if args.is_empty() {
            lines[0].push_str(suffix);
        } else {
            let count = args.len();
            let mut broke = false;
            for (index, arg) in args.iter().enumerate() {
                let segment = if index + 1 == count {
                    format!("{arg}]{suffix}")
                } else {
                    format!("{arg},")
                };
                let current = lines.last_mut().expect("a line");
                if index == 0 {
                    current.push_str(" [");
                    current.push_str(&segment);
                } else if current.chars().count() + 1 + segment.chars().count() <= WIDTH {
                    current.push(' ');
                    current.push_str(&segment);
                } else {
                    broke = true;
                    lines.push(format!("    {segment}"));
                }
            }
            if broke && args.iter().any(|arg| arg.contains(' ')) {
                return refuse("a wrapped suggestion with a reversed rule");
            }
        }
        if lines.iter().any(|line| line.chars().count() > WIDTH) {
            return refuse("a suggestion line wider than the pin's width");
        }
        Ok(format!("Try this:\n{}", lines.join("\n")))
    }

    /// `unresolveNameGlobalAvoidingLocals` (`src/Lean/ResolveName.lean:641-699`): the shortest
    /// suffix of an `export` alias, then of `_root_.name`, that resolves to exactly `name` and
    /// to no local.
    fn simulated_unresolve(
        &mut self,
        name: &Name,
        goal: &ProofGoal,
    ) -> Result<String, NatDefinitionElabError> {
        if name.has_macro_scopes() || self.source_scope.user_name(name) != *name {
            return refuse("a private or hygienic rule name");
        }
        let aliases = self
            .alias_cache
            .read(&self.txn.env)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let protected = self
            .protected_cache
            .read(&self.txn.env)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let namespace = name.parent();
        let mut initials = Vec::new();
        for (alias, targets) in aliases.entries() {
            if targets.contains(name) {
                // Only an alias in a parent namespace of the declaration's.
                let prefix = alias.parent();
                let mut cursor = namespace.clone();
                loop {
                    if cursor == prefix {
                        initials.push(alias.clone());
                        break;
                    }
                    if cursor.is_anonymous() {
                        break;
                    }
                    cursor = cursor.parent();
                }
            }
        }
        initials.push(Name::from_components(["_root_"]).append_core(name));
        for initial in initials {
            let mut components = Vec::new();
            let mut cursor = initial.clone();
            while !cursor.is_anonymous() {
                components.push(cursor.clone());
                cursor = cursor.parent();
            }
            let mut candidate = Name::anonymous();
            for component in &components {
                self.tick()?;
                let leaf = match component.leaf_view() {
                    LeafView::Str(text) => Name::str(Name::anonymous(), text),
                    LeafView::Num(value) => Name::num(Name::anonymous(), value),
                    LeafView::Anonymous => break,
                };
                candidate = leaf.append_core(&candidate);
                if self.simulated_names_local(&candidate, goal)? {
                    continue;
                }
                let resolved = self.source_scope.resolve_with_aliases(
                    &candidate,
                    |declaration| self.txn.env.contains(declaration),
                    &aliases,
                    &protected,
                );
                if matches!(resolved, Ok(Some(found)) if found == *name) {
                    return printable(&candidate).ok_or_else(|| {
                        error(TacticError::SimpSuggestionUnsupported(
                            "an unprintable name",
                        ))
                    });
                }
            }
        }
        printable(name).ok_or_else(|| {
            error(TacticError::SimpSuggestionUnsupported(
                "an unprintable name",
            ))
        })
    }

    /// `resolveLocalName` finds `candidate`: a local, a field of one, or the declaration
    /// being elaborated (its auxiliary local).
    fn simulated_names_local(
        &mut self,
        candidate: &Name,
        goal: &ProofGoal,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut prefix = candidate.clone();
        loop {
            if goal.lctx.find_by_user_name(&prefix).is_some() {
                return Ok(true);
            }
            if prefix.parent().is_anonymous() {
                break;
            }
            prefix = prefix.parent();
        }
        let mut namespace = self.source_scope.namespace.clone();
        loop {
            self.tick()?;
            let full = namespace.append_core(candidate);
            if self.defining.as_ref() == Some(&full)
                || self.recursion.as_ref().is_some_and(|r| r.name == full)
            {
                return Ok(true);
            }
            if namespace.is_anonymous() {
                return Ok(false);
            }
            namespace = namespace.parent();
        }
    }
}
