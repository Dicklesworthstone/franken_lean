//! Syntax quotations, antiquotations and the `macro`/`macro_rules` commands against the pinned
//! Reference (bead `fln-pin-syntax-corpus-7b5b`; `fln_parse`'s `quotations`).
//!
//! Each row is a command and the tree the pinned frontend produced for it, captured with
//! `scripts/extract/dump_command_syntax.lean` from `leanprover/lean4:v4.32.0` on 2026-10-09 from
//! one file holding the rows in this order (the pin elaborated it with one error, on `a2`'s
//! quotation, which is no parse error):
//!
//! ```text
//! T=~/.elan/toolchains/leanprover--lean4---v4.32.0
//! $T/bin/lean --run scripts/extract/dump_command_syntax.lean FILE.lean "$T"
//! ```
//!
//! The capture is `Syntax.toString`, with runs of whitespace collapsed to one space. Rows are
//! parsed in order under the file's grammar (Init's, then the file's own `syntax`), as the pin
//! parsed them. The last three rows are ordinary proofs: `with_reducible`'s sequence takes the `;`
//! after it, `fail`'s message sits in its optional slot, and `as_aux_lemma =>`'s sequence owns the
//! `<;>` of its last tactic (that row captured on its own the same day, the pin elaborating it
//! without a message). The two rows after it, captured together the same day without a message, are
//! a macro whose template is `{ tacs }` (`tacticSeqBracketed`, one tactic) and its use. The four
//! after them, captured together the same day without a message: a multi-line `{ …; try omega }`
//! template (a `try` outside every `do` block is the tactic's), its use, the same braces as a
//! whole `by`, and a parenthesized template whose `)` on its own line at the items' column ends the
//! sequence with an empty separator.
//! The seven after them, captured together the same day without a message: a `macro_rules`
//! template that is a tactic quotation with `first`'s alternatives on their own lines (the match
//! planner leaves a tactic quotation to the tactic parser), `solve | … | …` (census syntax whose
//! `group`s are `group` nodes), and `decreasing_with` taking the `;`-separated tactics after it.
//! The seven after them, captured together the same day without a message, are conv macros whose
//! templates are conv quotations (`(conv| …)`, `conv.quot` inside the `Term.quot` the pin reads a
//! category's quotation as), one conv tactic each: `tactic =>`/`tactic' =>` sequences, conv
//! leaves, `rewrite` with an antiquoted configuration and rules, and `first` with an antiquoted
//! sequence, as Init/Conv.lean's conv macros have them.
//! The four after them, captured together the same day without a message, are dynamic quotations
//! (`Term.dynamicQuot`, `(cat| …)` for a category with no quotation token of its own): `prec` and
//! `prio` numerals as macro templates (`macro "max" : prec => (prec| 1024)` in Init), a `term`
//! quotation, and a `prec` pattern holding `$num:num`.
//! The five after them, captured together the same day without a message: a file's own
//! non-associative `infix:25` beside the arrow, before it (`p ⊨ c → q`, the arrow being a trailing
//! parser with no left precedence) and inside its right-hand side (`q → p ⊨ f`), as Std's
//! `⊨` (LRAT `Entails`) is used.
//! The four after them, captured together the same day without a message: an `infix` whose
//! operator is a `unicode(…)` pair (`Syntax.unicodeAtom`, as Init/Notation.lean declares `≤`, `≥`,
//! `∧`, `∨`) and its uses under each spelling, one notation kind for both.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::parse_source_command;
use fln_syntax::tree::Syntax;

struct Accepted {
    source: &'static str,
    tree: &'static str,
}

const ROWS: &[Accepted] = &[
    Accepted {
        source: r#"syntax "dbl " term:max : term"#,
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"dbl \"")) (Syntax.cat `term [(precedence ":" (precMax "max"))])] ":" `term)"#,
    },
    Accepted {
        source: r#"macro_rules | `(dbl $x) => `($x + $x)"#,
        tree: r#"(Command.macro_rules [] [] (Term.attrKind []) "macro_rules" [] (Term.matchAlts [(Term.matchAlt "|" [[(Term.quot "`(" (termDbl_ "dbl" (term.pseudo.antiquot "$" [] `x [])) ")")]] "=>" (Term.quot "`(" («term_+_» (term.pseudo.antiquot "$" [] `x []) "+" (term.pseudo.antiquot "$" [] `x [])) ")"))]))"#,
    },
    Accepted {
        source: r#"macro "trip " x:term:max : term => `($x + $x + $x)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"trip \""))) (Command.macroArg [`x ":"] (Syntax.cat `term [(precedence ":" (precMax "max"))]))] (Command.macroTail ":" `term "=>" (Command.macroRhs (Term.quot "`(" («term_+_» («term_+_» (term.pseudo.antiquot "$" [] `x []) "+" (term.pseudo.antiquot "$" [] `x [])) "+" (term.pseudo.antiquot "$" [] `x [])) ")"))))"#,
    },
    Accepted {
        source: r#"macro "a1 " t:tactic : tactic => `(tactic| $t)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"a1 \""))) (Command.macroArg [`t ":"] (Syntax.cat `tactic []))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (tactic.pseudo.antiquot "$" [] `t []) ")"))))"#,
    },
    Accepted {
        source: r#"macro "a2 " t:tactic : tactic => `(tactic| $t; rfl)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"a2 \""))) (Command.macroArg [`t ":"] (Syntax.cat `tactic []))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quotSeq "`(tactic|" (Tactic.seq1 [(tactic.pseudo.antiquot "$" [] `t []) ";" (Tactic.tacticRfl "rfl")]) ")"))))"#,
    },
    Accepted {
        source: r#"macro "a3 " e:term : tactic => `(tactic| exact $e)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"a3 \""))) (Command.macroArg [`e ":"] (Syntax.cat `term []))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (Tactic.exact "exact" (term.pseudo.antiquot "$" [] `e [])) ")"))))"#,
    },
    Accepted {
        source: r#"macro "a4 " t:tacticSeq : tactic => `(tactic| (first | $t | rfl))"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"a4 \""))) (Command.macroArg [`t ":"] (Syntax.cat `tacticSeq []))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (Tactic.paren "(" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.first "first" [(group "|" (Tactic.tacticSeq.antiquot "$" [] `t [])) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])])) ")") ")"))))"#,
    },
    Accepted {
        source: r#"macro "a6 " x:ident : term => `(fun $x => $x)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"a6 \""))) (Command.macroArg [`x ":"] (Syntax.cat `ident []))] (Command.macroTail ":" `term "=>" (Command.macroRhs (Term.quot "`(" (Term.fun "fun" (Term.basicFun [(Term.funBinder.pseudo.antiquot "$" [] `x [])] [] "=>" (term.pseudo.antiquot "$" [] `x []))) ")"))))"#,
    },
    Accepted {
        source: r#"macro_rules | `(a7 $x:ident $y:term $(z)) => `($x)"#,
        tree: r#"(Command.macro_rules [] [] (Term.attrKind []) "macro_rules" [] (Term.matchAlts [(Term.matchAlt "|" [[(Term.quot "`(" (Term.app `a7 [(ident.antiquot "$" [] `x (antiquotName ":" "ident")) (term.pseudo.antiquot "$" [] `y (antiquotName ":" "term")) (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `z ")") [])]) ")")]] "=>" (Term.quot "`(" (term.pseudo.antiquot "$" [] `x []) ")"))]))"#,
    },
    Accepted {
        source: r#"macro "try' " t:tacticSeq : tactic => `(tactic| first | $t | skip)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"try' \""))) (Command.macroArg [`t ":"] (Syntax.cat `tacticSeq []))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (Tactic.first "first" [(group "|" (Tactic.tacticSeq.antiquot "$" [] `t [])) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip")])))]) ")"))))"#,
    },
    Accepted {
        source: r#"macro_rules
  | `(tactic| decreasing_trivial) =>
  `(tactic| with_reducible apply Nat.lt_irrefl; assumption)"#,
        tree: r#"(Command.macro_rules [] [] (Term.attrKind []) "macro_rules" [] (Term.matchAlts [(Term.matchAlt "|" [[(Tactic.quot "`(tactic|" (tacticDecreasing_trivial "decreasing_trivial") ")")]] "=>" (Tactic.quot "`(tactic|" (Tactic.withReducible "with_reducible" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.apply "apply" `Nat.lt_irrefl) ";" (Tactic.assumption "assumption")]))) ")"))]))"#,
    },
    Accepted {
        source: r#"theorem w1 : True := by with_reducible skip; trivial"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w1 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.withReducible "with_reducible" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip") ";" (Tactic.tacticTrivial "trivial")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"theorem w2 : True := by first | fail "no" | fail | trivial"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w2 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.fail "fail" [(str "\"no\"")])]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.fail "fail" [])]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")])))])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ax1 (a : Nat) (h : a = 1) : a = 1 ∧ True := by\n  as_aux_lemma =>\n    skip\n    constructor <;> first | exact h | trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ax1 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» `a "=" (num "1")) "∧" `True))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.as_aux_lemma "as_aux_lemma" "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip") [] (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h)]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")])))]))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"macro "my_triv" : tactic => `(tactic| { intros; trivial } )"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"my_triv\"")))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (Tactic.tacticSeqBracketed "{" [(Tactic.intros "intros" []) ";" (Tactic.tacticTrivial "trivial")] "}") ")"))))"#,
    },
    Accepted {
        source: r#"theorem b4 : True := by my_triv"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b4 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticMy_triv "my_triv")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"macro "my_order" : tactic => `(tactic| {
    simp only [Nat.lt_iff_add_one_le] at *;
    try omega })"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"my_order\"")))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (Tactic.tacticSeqBracketed "{" [(Tactic.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] `Nat.lt_iff_add_one_le)] "]"] [(Tactic.location "at" (Tactic.locationWildcard "*"))]) ";" (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))] "}") ")"))))"#,
    },
    Accepted {
        source: r#"theorem o1 (a b : Nat) (h : a < b) : a + 1 ≤ b := by my_order"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» `a "<" `b)] [] ")")] (Term.typeSpec ":" («term_≤_» («term_+_» `a "+" (num "1")) "≤" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticMy_order "my_order")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"theorem o2 (a : Nat) : a = a := by {
    skip;
    try rfl }"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o2 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeqBracketed "{" [(Tactic.skip "skip") ";" (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))] "}"))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"macro "my_tree_tac" : tactic => `(tactic|(
  subst_eqs
  repeat' split
  all_goals
    try simp only [Nat.add_zero] at *
  all_goals
    try assumption
    try contradiction
  all_goals
    subst_eqs
    omega
  ))"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"my_tree_tac\"")))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (Tactic.paren "(" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.substEqs "subst_eqs") [] (Tactic.repeat' "repeat'" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.split "split" [] [])]))) [] (Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] `Nat.add_zero)] "]"] [(Tactic.location "at" (Tactic.locationWildcard "*"))])])))]))) [] (Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.assumption "assumption")]))) [] (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.contradiction "contradiction")])))]))) [] (Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.substEqs "subst_eqs") [] (Tactic.omega "omega" (Tactic.optConfig []))]))) []])) ")") ")"))))"#,
    },
    Accepted {
        source: r#"syntax "my_trivial" : tactic"#,
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"my_trivial\""))] ":" `tactic)"#,
    },
    Accepted {
        source: r#"macro_rules | `(tactic| my_trivial) => `(tactic|
  first
  | exact True.intro
  | rfl
  | fail)"#,
        tree: r#"(Command.macro_rules [] [] (Term.attrKind []) "macro_rules" [] (Term.matchAlts [(Term.matchAlt "|" [[(Tactic.quot "`(tactic|" (tacticMy_trivial "my_trivial") ")")]] "=>" (Tactic.quot "`(tactic|" (Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `True.intro)]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.fail "fail" [])])))]) ")"))]))"#,
    },
    Accepted {
        source: r#"theorem tq1 : True := by my_trivial"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `tq1 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticMy_trivial "my_trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"theorem sv1 (p : Prop) (h : p) : p := by
  solve | exact h | assumption"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sv1 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.solveTactic "solve" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h)]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.assumption "assumption")])))])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"theorem sv2 : True := by
  · solve | apply True.intro | simp | fail "no""#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sv2 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.solveTactic "solve" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.apply "apply" `True.intro)]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.fail "fail" [(str "\"no\"")])])))])])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"macro "my_dec" : tactic =>
  `(tactic| first | rfl | skip; trivial)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"my_dec\"")))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip") ";" (Tactic.tacticTrivial "trivial")])))]) ")"))))"#,
    },
    Accepted {
        source: r#"macro "my_dec2" : tactic =>
  `(tactic| decreasing_with first | decreasing_trivial | subst_vars; decreasing_trivial)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"my_dec2\"")))] (Command.macroTail ":" `tactic "=>" (Command.macroRhs (Tactic.quot "`(tactic|" (tacticDecreasing_with_ "decreasing_with" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticDecreasing_trivial "decreasing_trivial")]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.substVars "subst_vars") ";" (tacticDecreasing_trivial "decreasing_trivial")])))])]))) ")"))))"#,
    },
    Accepted {
        source: r#"macro "conv_rows_rfl" : conv => `(conv| tactic => rfl)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"conv_rows_rfl\"")))] (Command.macroTail ":" `conv "=>" (Command.macroRhs (Term.quot (conv.quot "`(conv|" (Tactic.Conv.nestedTactic "tactic" "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) ")")))))"#,
    },
    Accepted {
        source: r#"macro "conv_rows_done" : conv => `(conv| tactic' => done)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"conv_rows_done\"")))] (Command.macroTail ":" `conv "=>" (Command.macroRhs (Term.quot (conv.quot "`(conv|" (Tactic.Conv.nestedTacticCore "tactic'" "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.done "done")]))) ")")))))"#,
    },
    Accepted {
        source: r#"macro "conv_rows_args" : conv => `(conv| congr)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"conv_rows_args\"")))] (Command.macroTail ":" `conv "=>" (Command.macroRhs (Term.quot (conv.quot "`(conv|" (Tactic.Conv.congr "congr") ")")))))"#,
    },
    Accepted {
        source: r#"macro "conv_rows_left" : conv => `(conv| lhs)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"conv_rows_left\"")))] (Command.macroTail ":" `conv "=>" (Command.macroRhs (Term.quot (conv.quot "`(conv|" (Tactic.Conv.lhs "lhs") ")")))))"#,
    },
    Accepted {
        source: r#"macro "conv_rows_apply " e:term : conv => `(conv| tactic => apply $e)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"conv_rows_apply \""))) (Command.macroArg [`e ":"] (Syntax.cat `term []))] (Command.macroTail ":" `conv "=>" (Command.macroRhs (Term.quot (conv.quot "`(conv|" (Tactic.Conv.nestedTactic "tactic" "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.apply "apply" (term.pseudo.antiquot "$" [] `e []))]))) ")")))))"#,
    },
    Accepted {
        source: r#"macro "conv_rows_rw" c:Lean.Parser.Tactic.optConfig s:Lean.Parser.Tactic.rwRuleSeq : conv => `(conv| rewrite $c:optConfig $s)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"conv_rows_rw\""))) (Command.macroArg [`c ":"] (Syntax.cat `Lean.Parser.Tactic.optConfig [])) (Command.macroArg [`s ":"] (Syntax.cat `Lean.Parser.Tactic.rwRuleSeq []))] (Command.macroTail ":" `conv "=>" (Command.macroRhs (Term.quot (conv.quot "`(conv|" (Tactic.Conv.rewrite "rewrite" (Tactic.optConfig.antiquot "$" [] `c (antiquotName ":" "optConfig")) (Tactic.rwRuleSeq.antiquot "$" [] `s [])) ")")))))"#,
    },
    Accepted {
        source: r#"macro "conv_rows_try " t:Lean.Parser.Tactic.Conv.convSeq : conv => `(conv| first | $t | skip)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"conv_rows_try \""))) (Command.macroArg [`t ":"] (Syntax.cat `Lean.Parser.Tactic.Conv.convSeq []))] (Command.macroTail ":" `conv "=>" (Command.macroRhs (Term.quot (conv.quot "`(conv|" (Tactic.Conv.first "first" [(group "|" (Tactic.Conv.convSeq.antiquot "$" [] `t [])) (group "|" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.skip "skip")])))]) ")")))))"#,
    },
    Accepted {
        source: r#"macro "dq_max" : prec => `(prec| 1024)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"dq_max\"")))] (Command.macroTail ":" `prec "=>" (Command.macroRhs (Term.dynamicQuot "`(" `prec "|" (num "1024") ")"))))"#,
    },
    Accepted {
        source: r#"macro "dq_low" : prio => `(prio| 100)"#,
        tree: r#"(Command.macro [] [] (Term.attrKind []) "macro" [] [] [] [(Command.macroArg [] (Syntax.atom (str "\"dq_low\"")))] (Command.macroTail ":" `prio "=>" (Command.macroRhs (Term.dynamicQuot "`(" `prio "|" (num "100") ")"))))"#,
    },
    Accepted {
        source: r#"def dq3 (t : Lean.Term) : Lean.MacroM Lean.Term := `(term| $t)"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dq3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`t] [":" `Lean.Term] [] ")")] [(Term.typeSpec ":" (Term.app `Lean.MacroM [`Lean.Term]))]) (Command.declValSimple ":=" (Term.dynamicQuot "`(" `term "|" (term.pseudo.antiquot "$" [] `t []) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: r#"def dq4 : Lean.Syntax → Option Nat
  | `(prec| $num:num) => some num.getNat
  | _ => none"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dq4 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Lean.Syntax "→" (Term.app `Option [`Nat])))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.dynamicQuot "`(" `prec "|" (num.antiquot "$" [] `num (antiquotName ":" "num")) ")")]] "=>" (Term.app `some [`num.getNat])) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `none)]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: r#"def MyE (a b : Nat) : Prop := a = b"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `MyE []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.prop "Prop"))]) (Command.declValSimple ":=" («term_=_» `a "=" `b) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: r#"infix:25 " ⊨ " => MyE"#,
        tree: r#"(Command.mixfix [] [] (Term.attrKind []) (Command.infix "infix") (precedence ":" (num "25")) [] [] (str "\" ⊨ \"") "=>" `MyE)"#,
    },
    Accepted {
        source: r#"theorem e1 (p c : Nat) : p ⊨ c → p ⊨ c := fun h => h"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `e1 []) (Command.declSig [(Term.explicitBinder "(" [`p `c] [":" `Nat] [] ")")] (Term.typeSpec ":" (Term.arrow («term_⊨_» `p "⊨" `c) "→" («term_⊨_» `p "⊨" `c)))) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`h] [] "=>" `h)) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"theorem e2 (p f : Nat) (q : Prop) (h : p ⊨ f) : q → p ⊨ f := fun _ => h"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `e2 []) (Command.declSig [(Term.explicitBinder "(" [`p `f] [":" `Nat] [] ")") (Term.explicitBinder "(" [`q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_⊨_» `p "⊨" `f)] [] ")")] (Term.typeSpec ":" (Term.arrow `q "→" («term_⊨_» `p "⊨" `f)))) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `h)) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"theorem e3 (p c : Nat) : p ⊨ c → True := fun _ => trivial"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `e3 []) (Command.declSig [(Term.explicitBinder "(" [`p `c] [":" `Nat] [] ")")] (Term.typeSpec ":" (Term.arrow («term_⊨_» `p "⊨" `c) "→" `True))) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `trivial)) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: r#"def MyLe (a b : Nat) : Prop := a ≤ b"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `MyLe []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.prop "Prop"))]) (Command.declValSimple ":=" («term_≤_» `a "≤" `b) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: r#"infix:50 unicode(" ≤≤ ", " =<<= ") => MyLe"#,
        tree: r#"(Command.mixfix [] [] (Term.attrKind []) (Command.infix "infix") (precedence ":" (num "50")) [] [] (Syntax.unicodeAtom "unicode(" (str "\" ≤≤ \"") "," (str "\" =<<= \"") [] ")") "=>" `MyLe)"#,
    },
    Accepted {
        source: r#"def ui1 : Prop := (1 : Nat) ≤≤ 2"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ui1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.prop "Prop"))]) (Command.declValSimple ":=" («term_≤≤_» (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (num "1") ":" [`Nat] ")") "≤≤" (num "2")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: r#"def ui2 : Prop := (1 : Nat) =<<= 2"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ui2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.prop "Prop"))]) (Command.declValSimple ":=" («term_≤≤_» (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (num "1") ":" [`Nat] ")") "=<<=" (num "2")) (Termination.suffix [] []) []) []))"#,
    },
];

fn render(syntax: &Syntax, out: &mut String) {
    match syntax {
        Syntax::Missing => out.push_str("<missing>"),
        Syntax::Atom { val, .. } => out.push_str(&format!("{:?}", val.as_str())),
        Syntax::Ident { val, .. } if val.is_anonymous() => out.push_str("`[anonymous]"),
        Syntax::Ident { val, .. } => {
            out.push('`');
            push_name(out, &name_parts(val));
        }
        Syntax::Node { kind, args, .. } => {
            if kind.to_display_string() == "null" {
                out.push('[');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    render(arg, out);
                }
                out.push(']');
                return;
            }
            let mut parts = name_parts(kind);
            if parts.len() > 2 && parts[0] == "Lean" && parts[1] == "Parser" {
                parts.drain(..2);
            }
            out.push('(');
            push_name(out, &parts);
            for arg in args {
                out.push(' ');
                render(arg, out);
            }
            out.push(')');
        }
    }
}

/// A name's own components (a component may hold dots).
fn name_parts(name: &Name) -> Vec<String> {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        parts.push(match cursor.leaf_view() {
            fln_core::name::LeafView::Str(part) => part.to_owned(),
            fln_core::name::LeafView::Num(part) => part.to_string(),
            fln_core::name::LeafView::Anonymous => String::new(),
        });
        cursor = cursor.parent();
    }
    parts.reverse();
    parts
}

/// `Name.toString` escapes each component on its own.
fn push_name(out: &mut String, parts: &[String]) {
    for (i, part) in parts.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        let plain = !part.is_empty()
            && part
                .chars()
                .all(|c| c.is_alphanumeric() || matches!(c, '_' | '!' | '?' | '\''));
        if plain {
            out.push_str(part);
        } else {
            out.push('«');
            out.push_str(part);
            out.push('»');
        }
    }
}

/// Parse `source` under `grammar` and register what it declares, as a file's command loop does.
/// A non-associative operator still refuses to chain, a file's own `infix` and `=` alike: only
/// the arrow takes one as its left operand (the rows above).
#[test]
fn non_associative_operators_still_refuse_to_chain() {
    let mut grammar = FileGrammar::new(false, &[], None).expect("Init");
    for source in [
        "def MyE (a b : Nat) : Prop := a = b",
        "infix:25 \" ⊨ \" => MyE",
    ] {
        parse(&mut grammar, source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
    for source in [
        "def en1 (p c : Nat) : Prop := p ⊨ c ⊨ c",
        "def en2 (a b c : Nat) : Prop := a = b = c",
    ] {
        assert!(parse(&mut grammar, source).is_err(), "{source}");
    }
}

fn parse(grammar: &mut FileGrammar, source: &str) -> Result<String, String> {
    let current = grammar.grammar();
    let parsed = with_grammar(&current, || parse_source_command(source.as_bytes()))
        .map_err(|error| format!("{error:?}"))?;
    grammar
        .declare(parsed.syntax())
        .map_err(|reason| reason.to_owned())?;
    let mut out = String::new();
    render(parsed.syntax(), &mut out);
    Ok(out)
}

#[test]
fn quotations_and_macros_produce_the_pins_trees() {
    let mut grammar = FileGrammar::new(false, &[], None).expect("Init");
    for row in ROWS {
        let ours = parse(&mut grammar, row.source)
            .unwrap_or_else(|error| panic!("{}: {error}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

/// Outside a quotation `$` starts no antiquotation, and the splices and escapes not read here are
/// refused rather than read as operators. `match $c with` is refused too: the pin reads an
/// antiquotation with no kind straight after `match` as its `(generalizing := …)` parameter and
/// then misses the discriminant.
#[test]
fn antiquotations_outside_quotations_and_unread_splices_are_refused() {
    let mut grammar = FileGrammar::new(false, &[], None).expect("Init");
    for source in [
        "def f (x : Nat) : Nat := $x",
        "def f (c : Lean.Term) : Lean.MacroM Lean.Term := `(match $c with | _ => 1)",
        "macro_rules | `(h [$xs,*]) => `([$xs,*])",
        "macro_rules | `(h $xs*) => `(g $xs*)",
        "macro_rules | `(h $$x) => `(g $x)",
        "macro_rules | `(h $x) => `(g $[$x]?)",
    ] {
        assert!(parse(&mut grammar, source).is_err(), "{source}");
    }
}
