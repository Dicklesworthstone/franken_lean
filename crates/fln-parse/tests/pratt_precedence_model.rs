//! `pratt_precedence_model` — the precedence table, pinned against the pin's own evaluated results
//! (bead fln-ffam).
//!
//! ## Why the oracle is the pin and not my parser
//!
//! This is where the differential-limits law bites hardest. A precedence model that is wrong in the
//! same direction as the parser built from it produces perfect agreement — and agreement is all
//! that a round-trip or an incremental-vs-from-scratch comparison measures. Both would be green
//! with `*` binding looser than `+` throughout.
//!
//! So the model is pinned against **observations of the running Reference**. Each case below is an
//! expression whose *value* discriminates the grouping, together with the value the pinned `lean`
//! binary actually printed for it. The model groups the expression; a tiny evaluator computes the
//! grouped tree; the result must equal what the pin printed. A shared mistake cannot survive that,
//! because the pin does not share it.
//!
//! ## The observations
//!
//! Taken by running `~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean` on `#eval <expr>`:
//!
//! ```text
//! 2 + 3 * 4              -> 14      `*` binds tighter than `+`      (else 20)
//! 2 * 3 + 4              -> 10      the same, other order            (else 14)
//! 2 * 3 ^ 2              -> 18      `^` binds tighter than `*`       (else 36)
//! 2 ^ 3 ^ 2              -> 512     `^` is RIGHT associative         (else 64)
//! 10 - 3 - 4             -> 3       `-` is LEFT associative          (else 11)
//! true || false && false -> true    `&&` binds tighter than `||`     (else false)
//! ```
//!
//! Each parenthesised alternative is the value the *other* grouping would produce, so every case
//! carries information. One candidate was **rejected** for carrying none: `true && false || true`
//! evaluates to `true` under either grouping, so observing `true` would have proved nothing. That
//! rejection is recorded because a discriminating-case table is only as good as its worst row.
//!
//! ## The declared precedences, cited
//!
//! From `Init/Notation.lean` at the pinned tag, and two of them are values I would have got wrong
//! from memory — which is the argument for citing rather than recalling:
//!
//! ```text
//! +   infixl:65   :284
//! -   infixl:65   :285
//! *   infixl:70   :286
//! ^   infixr:80   :291     NOT 75
//! =   infix:50    :379
//! &&  infixl:35   :412     infixL, not infixr
//! ||  infixl:30   :413     infixL, not infixr
//! ```

#![forbid(unsafe_code)]

use fln_parse::state::Prec;

/// How a binary operator associates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Assoc {
    Left,
    Right,
    /// `infix` with no side: the operator does not chain, so `a = b = c` is not a parse.
    None,
}

/// One row of the precedence table, with the pin line it was read from.
#[derive(Debug, Clone, Copy)]
struct Op {
    symbol: &'static str,
    prec: Prec,
    assoc: Assoc,
    /// The `Init/Notation.lean` line, so a reader can check the row rather than trust it.
    cite: u32,
}

/// The table under test. Transcribed with citations; validated below against evaluated results.
const TABLE: &[Op] = &[
    Op {
        symbol: "^",
        prec: 80,
        assoc: Assoc::Right,
        cite: 291,
    },
    Op {
        symbol: "*",
        prec: 70,
        assoc: Assoc::Left,
        cite: 286,
    },
    Op {
        symbol: "+",
        prec: 65,
        assoc: Assoc::Left,
        cite: 284,
    },
    Op {
        symbol: "-",
        prec: 65,
        assoc: Assoc::Left,
        cite: 285,
    },
    Op {
        symbol: "=",
        prec: 50,
        assoc: Assoc::None,
        cite: 379,
    },
    Op {
        symbol: "&&",
        prec: 35,
        assoc: Assoc::Left,
        cite: 412,
    },
    Op {
        symbol: "||",
        prec: 30,
        assoc: Assoc::Left,
        cite: 413,
    },
];

fn op(symbol: &str) -> Op {
    *TABLE
        .iter()
        .find(|entry| entry.symbol == symbol)
        .unwrap_or_else(|| unreachable_row(symbol))
}

/// A missing table row is a defect in the test's own table, reported as a comparison.
fn unreachable_row(symbol: &str) -> &'static Op {
    assert_eq!(symbol, "<a symbol in TABLE>", "no table row for {symbol:?}");
    &TABLE[0]
}

/// A grouped expression — the shape the model claims a token sequence has.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tree {
    Num(i64),
    Bool(bool),
    Bin(String, Box<Tree>, Box<Tree>),
}

impl Tree {
    /// The fully-parenthesised rendering, so a grouping is comparable as a string.
    fn render(&self) -> String {
        match self {
            Tree::Num(value) => value.to_string(),
            Tree::Bool(value) => value.to_string(),
            Tree::Bin(symbol, left, right) => {
                format!("({} {} {})", left.render(), symbol, right.render())
            }
        }
    }
}

/// Group a flat operand/operator sequence by the table — the model itself.
///
/// Precedence climbing, which is the same shape the Pratt loop runs: parse a leading operand, then
/// take trailing operators while they bind at least as tightly as the context demands. The
/// right-hand side of a left-associative operator is parsed at `prec + 1` so an equal-precedence
/// operator does not get absorbed; for a right-associative one it is parsed at `prec`, which is
/// what makes it chain rightward.
fn group(operands: &[Tree], operators: &[&str]) -> Result<Tree, String> {
    if operands.len() != operators.len() + 1 {
        return Err(format!(
            "{} operands need {} operators, got {}",
            operands.len(),
            operands.len() - 1,
            operators.len()
        ));
    }
    let mut index = 0usize;
    let tree = climb(operands, operators, &mut index, 0)?;
    if index != operators.len() {
        return Err(format!(
            "stopped after {index} of {} operators — a non-associative operator refused to chain",
            operators.len()
        ));
    }
    Ok(tree)
}

/// The requirement each side of an operator imposes, which is how the pin desugars a fixity
/// declaration: `infixl:65 a + b` becomes `a:65 + b:66`, `infixr:80` becomes `a:81 ^ b:80`, and a
/// non-associative `infix:50` becomes `a:51 = b:51`.
///
/// Both sides matter, and modelling only the right-hand one is a real defect I made and the tests
/// caught: without the LEFT requirement, `1 = 2 = 3` chains happily as `((1 = 2) = 3)`. The left
/// requirement is this model's form of `checkLhsPrec`, and its presence here is slice A's rule 2 —
/// leading *and* trailing sides check precedence — showing up where it is observable.
fn sides(entry: Op) -> (Prec, Prec) {
    match entry.assoc {
        Assoc::Left => (entry.prec, entry.prec + 1),
        Assoc::Right => (entry.prec + 1, entry.prec),
        Assoc::None => (entry.prec + 1, entry.prec + 1),
    }
}

fn climb(
    operands: &[Tree],
    operators: &[&str],
    index: &mut usize,
    min_prec: Prec,
) -> Result<Tree, String> {
    let mut left = operands[*index].clone();
    // An atom binds as tightly as anything can; a built node binds at its operator's level. This
    // is `lhsPrec`.
    let mut left_prec = MAX_MODEL_PREC;
    while *index < operators.len() {
        let entry = op(operators[*index]);
        let (needs_left, needs_right) = sides(entry);
        if entry.prec < min_prec {
            break;
        }
        // checkLhsPrec: what we already have must bind tightly enough to be this operator's left
        // argument. This is what stops a non-associative operator from chaining.
        if left_prec < needs_left {
            break;
        }
        *index += 1;
        let right = climb(operands, operators, index, needs_right)?;
        left = Tree::Bin(entry.symbol.to_string(), Box::new(left), Box::new(right));
        left_prec = entry.prec;
    }
    Ok(left)
}

/// Above every level in the table — an atom's `lhsPrec`.
const MAX_MODEL_PREC: Prec = 1024;

/// Evaluate a grouped tree, so the model's grouping can be compared against a value the pin
/// printed. Deliberately tiny: it exists to turn a shape into the pin's own currency.
fn eval(tree: &Tree) -> Result<Value, String> {
    match tree {
        Tree::Num(value) => Ok(Value::Num(*value)),
        Tree::Bool(value) => Ok(Value::Bool(*value)),
        Tree::Bin(symbol, left, right) => {
            let left = eval(left)?;
            let right = eval(right)?;
            match (symbol.as_str(), left, right) {
                ("+", Value::Num(a), Value::Num(b)) => Ok(Value::Num(a + b)),
                ("-", Value::Num(a), Value::Num(b)) => Ok(Value::Num(a - b)),
                ("*", Value::Num(a), Value::Num(b)) => Ok(Value::Num(a * b)),
                ("^", Value::Num(a), Value::Num(b)) => Ok(Value::Num(
                    a.pow(u32::try_from(b).map_err(|_| "exponent out of range".to_string())?),
                )),
                ("=", Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a == b)),
                ("&&", Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a && b)),
                ("||", Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a || b)),
                (symbol, a, b) => Err(format!("cannot evaluate {a:?} {symbol} {b:?}")),
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Value {
    Num(i64),
    Bool(bool),
}

impl Value {
    /// Rendered as the pin's `#eval` prints it, so the comparison is against the observed text.
    fn render(self) -> String {
        match self {
            Value::Num(value) => value.to_string(),
            Value::Bool(value) => value.to_string(),
        }
    }
}

fn num(value: i64) -> Tree {
    Tree::Num(value)
}

fn boolean(value: bool) -> Tree {
    Tree::Bool(value)
}

/// One observation: the expression, its operands and operators, what the pin printed, and what the
/// *other* grouping would have printed.
struct Observation {
    source: &'static str,
    operands: Vec<Tree>,
    operators: Vec<&'static str>,
    /// What the pinned `lean` binary printed for `#eval <source>`.
    pin_printed: &'static str,
    /// What the wrong grouping would print. Recorded so every row is provably discriminating.
    wrong_grouping_would_print: &'static str,
    expected_shape: &'static str,
}

fn observations() -> Vec<Observation> {
    vec![
        Observation {
            source: "2 + 3 * 4",
            operands: vec![num(2), num(3), num(4)],
            operators: vec!["+", "*"],
            pin_printed: "14",
            wrong_grouping_would_print: "20",
            expected_shape: "(2 + (3 * 4))",
        },
        Observation {
            source: "2 * 3 + 4",
            operands: vec![num(2), num(3), num(4)],
            operators: vec!["*", "+"],
            pin_printed: "10",
            wrong_grouping_would_print: "14",
            expected_shape: "((2 * 3) + 4)",
        },
        Observation {
            source: "2 * 3 ^ 2",
            operands: vec![num(2), num(3), num(2)],
            operators: vec!["*", "^"],
            pin_printed: "18",
            wrong_grouping_would_print: "36",
            expected_shape: "(2 * (3 ^ 2))",
        },
        Observation {
            source: "2 ^ 3 ^ 2",
            operands: vec![num(2), num(3), num(2)],
            operators: vec!["^", "^"],
            pin_printed: "512",
            wrong_grouping_would_print: "64",
            expected_shape: "(2 ^ (3 ^ 2))",
        },
        Observation {
            source: "10 - 3 - 4",
            operands: vec![num(10), num(3), num(4)],
            operators: vec!["-", "-"],
            pin_printed: "3",
            wrong_grouping_would_print: "11",
            expected_shape: "((10 - 3) - 4)",
        },
        Observation {
            source: "true || false && false",
            operands: vec![boolean(true), boolean(false), boolean(false)],
            operators: vec!["||", "&&"],
            pin_printed: "true",
            wrong_grouping_would_print: "false",
            expected_shape: "(true || (false && false))",
        },
    ]
}

/// **THE MODEL IS PINNED AGAINST THE PIN'S OWN RESULTS.**
///
/// For each observation the model groups the expression, the grouped tree is evaluated, and the
/// value must equal what the pinned binary printed. The grouping shape is asserted too, so a
/// failure says whether the model grouped wrongly or the evaluator disagreed.
#[test]
fn the_model_reproduces_every_value_the_pin_printed() {
    for case in observations() {
        let tree = group(&case.operands, &case.operators).unwrap_or_else(|error| {
            assert_eq!(error, "", "{}: the model refused to group", case.source);
            Tree::Num(0)
        });

        assert_eq!(
            tree.render(),
            case.expected_shape,
            "{}: the model grouped differently than the pin's value implies",
            case.source
        );

        let value = eval(&tree).unwrap_or_else(|error| {
            assert_eq!(error, "", "{}: could not evaluate", case.source);
            Value::Num(0)
        });
        assert_eq!(
            value.render(),
            case.pin_printed,
            "{}: the model's grouping evaluates to {} but the PIN printed {}. This is the \
             assertion a self-differential cannot make — my parser agreeing with my model proves \
             nothing if both are wrong.",
            case.source,
            value.render(),
            case.pin_printed
        );
    }
}

/// **Every observation is discriminating.** The other grouping must produce a *different* value —
/// otherwise the row carries no information and the suite above is partly decorative.
///
/// One candidate was rejected on exactly this test: `true && false || true` evaluates to `true`
/// under either grouping, so observing `true` proves nothing about precedence. Recorded because a
/// table of discriminating cases is only as good as its worst row.
#[test]
fn every_observation_actually_discriminates_the_grouping() {
    for case in observations() {
        assert_ne!(
            case.pin_printed, case.wrong_grouping_would_print,
            "{}: the two groupings produce the same value, so this row proves nothing",
            case.source
        );

        // And the wrong grouping is reachable: flipping the table's ordering for this case must
        // actually produce the other value, so the claim is measured rather than asserted.
        let flipped = group_with_flipped_table(&case.operands, &case.operators);
        if let Ok(tree) = flipped
            && let Ok(value) = eval(&tree)
        {
            {
                assert_eq!(
                    value.render(),
                    case.wrong_grouping_would_print,
                    "{}: inverting the table must produce the recorded wrong value, or the \
                     recorded value is not what a wrong table actually gives",
                    case.source
                );
            }
        }
    }
}

/// Group with the table inverted — precedence order reversed AND associativity swapped.
///
/// This is what a table that is wrong in one consistent direction produces, which is the mistake a
/// self-differential cannot see: a parser built from this table agrees with itself perfectly.
/// Associativity has to be flipped too, because for `2 ^ 3 ^ 2` both operators are the same and
/// only the associativity decides the grouping — which the test caught when I flipped precedence
/// alone.
fn group_with_flipped_table(operands: &[Tree], operators: &[&str]) -> Result<Tree, String> {
    fn flipped(symbol: &str) -> Op {
        let entry = op(symbol);
        Op {
            symbol: entry.symbol,
            prec: 110 - entry.prec,
            assoc: match entry.assoc {
                Assoc::Left => Assoc::Right,
                Assoc::Right => Assoc::Left,
                Assoc::None => Assoc::None,
            },
            cite: entry.cite,
        }
    }
    fn climb_flipped(
        operands: &[Tree],
        operators: &[&str],
        index: &mut usize,
        min_prec: Prec,
    ) -> Result<Tree, String> {
        let mut left = operands[*index].clone();
        let mut left_prec = MAX_MODEL_PREC;
        while *index < operators.len() {
            let entry = flipped(operators[*index]);
            let (needs_left, needs_right) = sides(entry);
            if entry.prec < min_prec || left_prec < needs_left {
                break;
            }
            *index += 1;
            let right = climb_flipped(operands, operators, index, needs_right)?;
            left = Tree::Bin(entry.symbol.to_string(), Box::new(left), Box::new(right));
            left_prec = entry.prec;
        }
        Ok(left)
    }
    let mut index = 0usize;
    climb_flipped(operands, operators, &mut index, 0)
}

/// A non-associative operator refuses to chain, which is what the pin does with `1 = 2 = 3`:
/// observed in slice B as one error at the leftover `=` reported from the command level, meaning
/// the term parser stopped rather than producing a chained tree.
#[test]
fn a_non_associative_operator_refuses_to_chain() {
    let refused = group(&[num(1), num(2), num(3)], &["=", "="]);
    assert!(
        refused.is_err(),
        "`1 = 2 = 3` must not group; the pin stops the trailing chain there. Got {:?}",
        refused.map(|tree| tree.render())
    );

    // A single application is fine, so the refusal is about chaining and not about the operator.
    assert_eq!(
        group(&[num(1), num(2)], &["="])
            .expect("a single = groups")
            .render(),
        "(1 = 2)"
    );
}

/// `=` binds looser than `+`, so `1 + 2 = 3` groups as `((1 + 2) = 3)`. The pin evaluates it to
/// `true`, which is only possible under that grouping — the other one is not even well typed.
#[test]
fn comparison_binds_looser_than_arithmetic() {
    let tree = group(&[num(1), num(2), num(3)], &["+", "="]).expect("groups");
    assert_eq!(tree.render(), "((1 + 2) = 3)");
    assert_eq!(
        eval(&tree).expect("evaluates").render(),
        "true",
        "the pin printed `true` for `#eval 1 + 2 = 3`"
    );
}

/// The table's rows carry citations and are internally consistent: strictly ordered where the
/// observations require it, and no duplicate symbols.
#[test]
fn the_table_is_consistent_with_the_orderings_the_observations_prove() {
    assert!(
        op("^").prec > op("*").prec,
        "`2 * 3 ^ 2` = 18 requires ^ tighter than *"
    );
    assert!(
        op("*").prec > op("+").prec,
        "`2 + 3 * 4` = 14 requires * tighter than +"
    );
    assert_eq!(
        op("+").prec,
        op("-").prec,
        "+ and - share a level (both infixl:65)"
    );
    assert!(
        op("+").prec > op("=").prec,
        "`1 + 2 = 3` = true requires + tighter than ="
    );
    assert!(
        op("&&").prec > op("||").prec,
        "`true || false && false` = true requires && tighter than ||"
    );
    assert_eq!(op("^").assoc, Assoc::Right, "`2 ^ 3 ^ 2` = 512");
    assert_eq!(op("-").assoc, Assoc::Left, "`10 - 3 - 4` = 3");
    assert_eq!(
        op("&&").assoc,
        Assoc::Left,
        "infixl:35 at Notation.lean:412 — infixL, which is not what other languages would suggest"
    );

    // Every row cites a line, and the citations are in the file's range.
    for entry in TABLE {
        assert!(
            entry.cite > 200 && entry.cite < 500,
            "row {:?} cites Notation.lean:{}, which is outside the plausible range",
            entry.symbol,
            entry.cite
        );
    }
    // No duplicate symbols, which would make `op` return whichever came first.
    let mut symbols: Vec<&str> = TABLE.iter().map(|entry| entry.symbol).collect();
    symbols.sort_unstable();
    let count = symbols.len();
    symbols.dedup();
    assert_eq!(symbols.len(), count, "duplicate symbol in the table");
}

/// The model's precedence numbers match the engine's constants where they overlap, so the two
/// cannot drift apart silently.
#[test]
fn the_models_levels_sit_below_the_engines_max_prec() {
    use fln_parse::state::{ARG_PREC, LEAD_PREC, MAX_PREC};
    for entry in TABLE {
        assert!(
            entry.prec < MAX_PREC,
            "{:?} at {} must sit below maxPrec {MAX_PREC}",
            entry.symbol,
            entry.prec
        );
    }
    // Compared as values, so the assertion is about the constants rather than a comparison the
    // compiler folds away to `true`.
    assert_eq!(
        (MAX_PREC, ARG_PREC, LEAD_PREC),
        (1024, 1023, 1022),
        "the pin's maxPrec/argPrec/leadPrec, which the engine's constants must match"
    );
}
