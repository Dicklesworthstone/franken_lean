//! Whole-command parse trees against the pinned Reference (bead `franken_lean-z8j.1.10`,
//! stage 2: builtin parsers producing the pin's node kinds).
//!
//! Each row is a complete command and the tree the pinned frontend produced for it, captured
//! with `scripts/extract/dump_command_syntax.lean` from `leanprover/lean4:v4.32.0` (commit
//! `8c9756b28d64dab099da31a4c09229a9e6a2ef35`) on 2026-10-05:
//!
//! ```text
//! T=~/.elan/toolchains/leanprover--lean4---v4.32.0
//! $T/bin/lean --run scripts/extract/dump_command_syntax.lean FILE.lean "$T"
//! ```
//!
//! The capture is `Syntax.toString`, with runs of whitespace collapsed to one space. There is no
//! update mode: a row changes only by re-running the capture and reviewing the difference.
//!
//! The comparison is exact over node kinds, child order, null nodes, atom spellings and
//! identifier names, through [`render`], which prints FrankenLean's tree in the same vocabulary.
//! It excludes source positions and trivia. The tree on our side is the one the check-source
//! engine elaborates: `parse_definition`'s.

#![forbid(unsafe_code)]

use fln_parse::{DefinitionParseError, NatDefinitionParseError, parse_definition};
use fln_syntax::source::BytePos;
use fln_syntax::tree::Syntax;

/// A command the pin accepts, and its tree.
struct Accepted {
    source: &'static str,
    tree: &'static str,
}

/// A command the pin refuses, the pin's message, and the byte of the token it names.
struct Refused {
    source: &'static str,
    message: &'static str,
    at: usize,
}

/// Inline attributes, `declModifiers` slot 1: `Term.attributes` over the `attr` and `prio`
/// categories (`Lean/Parser/Term.lean`, `Lean/Parser/Attr.lean`, `Init/Notation.lean`,
/// `Init/Tactics.lean`, `Init/Grind/Attr.lean`). Captured 2026-10-08 from one file the pin
/// elaborated without an error, in this order, after `def wrap (n : Nat) : Nat := n`; the two
/// `scoped`/`local` rows sat inside `namespace N`.
const ATTRIBUTES: &[Accepted] = &[
    Accepted {
        source: "@[simp high] theorem t1 (n : Nat) : wrap n = n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] [] [(prioHigh "high")]))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `wrap [`n]) "=" `n))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[simp ← (low)] theorem t2 (n : Nat) : n = wrap n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] ["←"] [(«prio(_)» "(" (prioLow "low") ")")]))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" (Term.app `wrap [`n])))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[simp ↓ 1001] theorem t3 (n : Nat) : wrap (wrap n) = n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [(Tactic.simpPre "↓")] [] [(num "1001")]))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `wrap [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `wrap [`n]) ")")]) "=" `n))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[simp, grind =] theorem t4 (n : Nat) : wrap (wrap (wrap n)) = n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] [] [])) "," (Term.attrInstance (Term.attrKind []) (Attr.grind "grind" [(Attr.grindMod (Attr.grindEq "=" []))]))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `wrap [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `wrap [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `wrap [`n]) ")")]) ")")]) "=" `n))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[grind _=_] theorem t5 (n : Nat) : wrap (n + 0) = wrap n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.grind "grind" [(Attr.grindMod (Attr.grindEqBoth "_" "=" "_" []))]))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t5 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `wrap [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `n "+" (num "0")) ")")]) "=" (Term.app `wrap [`n])))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[inline] def f1 (n : Nat) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `inline []))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[specialize] def f2 (g : Nat → Nat) (n : Nat) : Nat := g n",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.specialize "specialize" []))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`g] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `g [`n]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: r#"@[deprecated wrap (since := "2026-01-01")] def f3 (n : Nat) : Nat := n"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Lean.deprecated "deprecated" [`wrap] [] ["(" "since" ":=" (str "\"2026-01-01\"") ")"]))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: r#"@[deprecated "use wrap"] def f3b (n : Nat) : Nat := n"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Lean.deprecated "deprecated" [] [(str "\"use wrap\"")] []))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f3b []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[inherit_doc wrap] def f4 (n : Nat) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `inherit_doc [`wrap]))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: r#"@[extern "lean_fln_probe"] def f5 (n : Nat) : Nat := n"#,
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.extern "extern" [(Attr.externEntry [] [] (str "\"lean_fln_probe\""))]))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[implemented_by f1] def f6 (n : Nat) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `implemented_by [`f1]))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f6 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[reducible, macro_inline] def f7 (n : Nat) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible [])) "," (Term.attrInstance (Term.attrKind []) (Attr.simple `macro_inline []))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f7 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[export lean_fln_probe_export] def f8 (n : Nat) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.export "export" `lean_fln_probe_export))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f8 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[instance] def f9 : Inhabited Nat := Inhabited.mk 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.instance "instance" []))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `f9 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Inhabited [`Nat]))]) (Command.declValSimple ":=" (Term.app `Inhabited.mk [(num "0")]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[scoped simp] theorem t6 (n : Nat) : wrap n + 0 = wrap n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind [(Term.scoped "scoped")]) (Attr.simp "simp" [] [] []))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t6 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» (Term.app `wrap [`n]) "+" (num "0")) "=" (Term.app `wrap [`n])))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[local simp mid] theorem t7 (n : Nat) : 0 + wrap n = wrap n := Nat.zero_add _",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind [(Term.local "local")]) (Attr.simp "simp" [] [] [(prioMid "mid")]))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t7 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» (num "0") "+" (Term.app `wrap [`n])) "=" (Term.app `wrap [`n])))) (Command.declValSimple ":=" (Term.app `Nat.zero_add [(Term.hole "_")]) (Termination.suffix [] []) [])))"#,
    },
];

/// The `if` notations (`termIfThenElse`, and `termDepIfThenElse` with evidence). Captured
/// 2026-10-08 from one file the pin elaborated without an error.
const CONDITIONALS: &[Accepted] = &[
    Accepted {
        source: "def ifs (n : Nat) : Nat := if n = 0 then 1 else n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ifs []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" (num "1") "else" `n) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def difs (n : Nat) : Nat := if h : n = 0 then 1 else n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `difs []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "1") "else" `n) (Termination.suffix [] []) []) []))"#,
    },
];

/// Init's plain infix notations (`Init/Notation.lean:272-428`, `Init/Core.lean:539`) and
/// binder groups without a type (`bracketedBinder (requireType := false)`,
/// `Lean/Parser/Term.lean`). Captured 2026-10-08 from one file the pin elaborated without an
/// error, in this order.
const INFIXES_AND_UNTYPED_BINDERS: &[Accepted] = &[
    Accepted {
        source: "def p1 (f : Nat → Nat) (a : Nat) : Nat := f <| a",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_<|_» `f "<|" `a) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def p2 (f g : Nat → Nat) (a : Nat) : Nat := f <| g <| a + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f `g] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_<|_» `f "<|" («term_<|_» `g "<|" («term_+_» `a "+" (num "1")))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def s1 (α β : Type) : Type := α × β",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `s1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`α `β] [":" (Term.type "Type" [])] [] ")")] [(Term.typeSpec ":" (Term.type "Type" []))]) (Command.declValSimple ":=" («term_×_» `α "×" `β) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem m1 (xs : List Nat) (h : 1 ∈ xs) : 1 ∈ xs := h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `m1 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∈_» (num "1") "∈" `xs)] [] ")")] (Term.typeSpec ":" («term_∈_» (num "1") "∈" `xs))) (Command.declValSimple ":=" `h (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem m2 (xs : List Nat) (h : 1 ∉ xs) : 1 ∉ xs := h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `m2 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∉_» (num "1") "∉" `xs)] [] ")")] (Term.typeSpec ":" («term_∉_» (num "1") "∉" `xs))) (Command.declValSimple ":=" `h (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def c1 (f g : Nat → Nat) : Nat → Nat := f ∘ g",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f `g] [":" (Term.arrow `Nat "→" `Nat)] [] ")")] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" («term_∘_» `f "∘" `g) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem d1 (h : 2 ∣ 4) : 2 ∣ 4 := h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `d1 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" («term_∣_» (num "2") "∣" (num "4"))] [] ")")] (Term.typeSpec ":" («term_∣_» (num "2") "∣" (num "4")))) (Command.declValSimple ":=" `h (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def u1 (f : Nat → Nat) (x : Option Nat) : Option Nat := f <$> x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `u1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`x] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_<$>_» `f "<$>" `x) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem s2 (a b : List Nat) (h : a ⊆ b) : a ⊆ b := h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`h] [":" («term_⊆_» `a "⊆" `b)] [] ")")] (Term.typeSpec ":" («term_⊆_» `a "⊆" `b))) (Command.declValSimple ":=" `h (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem i1 {α} (a : α) : a = a := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `i1 []) (Command.declSig [(Term.implicitBinder "{" [`α] [] "}") (Term.explicitBinder "(" [`a] [":" `α] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def i2 {α β} (f : α → β) (a : α) : β := f a",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `i2 []) (Command.optDeclSig [(Term.implicitBinder "{" [`α `β] [] "}") (Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")") (Term.explicitBinder "(" [`a] [":" `α] [] ")")] [(Term.typeSpec ":" `β)]) (Command.declValSimple ":=" (Term.app `f [`a]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem i3 ⦃n⦄ (h : n = 1) : n = 1 := h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `i3 []) (Command.declSig [(Term.strictImplicitBinder "⦃" [`n] [] "⦄") (Term.explicitBinder "(" [`h] [":" («term_=_» `n "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" (num "1")))) (Command.declValSimple ":=" `h (Termination.suffix [] []) [])))"#,
    },
];

/// Declaration modifiers, `declModifiers` slots 2..6 (`Lean/Parser/Command.lean:114`).
const MODIFIERS: &[Accepted] = &[
    Accepted {
        source: "protected def bar : Nat := 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [(Command.protected "protected")] [] [] []) (Command.definition "def" (Command.declId `bar []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private def a : Nat := 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.definition "def" (Command.declId `a []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "noncomputable def b : Nat := 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [(Command.noncomputable "noncomputable")] [] []) (Command.definition "def" (Command.declId `b []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "2") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private protected noncomputable unsafe partial def c (n : Nat) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [(Command.protected "protected")] [(Command.noncomputable "noncomputable")] [(Command.unsafe "unsafe")] [(Command.partial "partial")]) (Command.definition "def" (Command.declId `c []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[simp] protected theorem d : 1 = 1 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] [] []))] "]")] [] [(Command.protected "protected")] [] [] []) (Command.theorem "theorem" (Command.declId `d []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (num "1") "=" (num "1")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "protected theorem e : 2 = 2 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [(Command.protected "protected")] [] [] []) (Command.theorem "theorem" (Command.declId `e []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (num "2") "=" (num "2")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "nonrec def f : Nat := 3",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] [(Command.nonrec "nonrec")]) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "3") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "public def g : Nat := 4",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.public "public")] [] [] [] []) (Command.definition "def" (Command.declId `g []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "4") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private\ndef h : Nat := 5",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.definition "def" (Command.declId `h []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "5") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "unsafe def i : Nat := 6",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [(Command.unsafe "unsafe")] []) (Command.definition "def" (Command.declId `i []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "6") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "private example : 1 = 1 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.example "example" (Command.optDeclSig [] [(Term.typeSpec ":" («term_=_» (num "1") "=" (num "1")))]) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
];

/// `instance` without a name (`optional declId`): the elaborator generates the name.
const ANONYMOUS_INSTANCES: &[Accepted] = &[
    Accepted {
        source: "instance : Inhabited Nat := Inhabited.mk 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.app `Inhabited.mk [(num "0")]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "instance (priority := 50) : Inhabited Nat := Inhabited.mk 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [(Command.namedPrio "(" "priority" ":=" (num "50") ")")] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.app `Inhabited.mk [(num "0")]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "instance {α : Type} [Inhabited α] : Inhabited (List α) := Inhabited.mk []",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [])] "}") (Term.instBinder "[" [] (Term.app `Inhabited [`α]) "]")] (Term.typeSpec ":" (Term.app `Inhabited [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `List [`α]) ")")]))) (Command.declValSimple ":=" (Term.app `Inhabited.mk [(«term[_]» "[" [] "]")]) (Termination.suffix [] []) [])))"#,
    },
];

/// `⟨a, b, …⟩`: `Term.anonymousCtor`, `"⟨" >> sepBy termParser ", " (allowTrailingSep := true)
/// >> "⟩"` (`Lean/Parser/Term.lean:216`), alone, nested, with a trailing comma, as a do-`let`
/// pattern, and inside a list. The Point rows were captured after
/// `structure Point where x : Nat y : Nat`, and the do row after
/// `structure P where a : Nat b : Nat`.
const ANONYMOUS_CONSTRUCTORS: &[Accepted] = &[
    Accepted {
        source: "theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [`hp "," `hq] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def u : Unit := ⟨⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `u []) (Command.optDeclSig [] [(Term.typeSpec ":" `Unit)]) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [] "⟩") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "instance : Add P := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Add [`P]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.anonymousCtor "⟨" [(«term_+_» `a.x "+" `b.x) "," («term_+_» `a.y "+" `b.y)] "⟩")))] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def p : Point := ⟨1, 2,⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p []) (Command.optDeclSig [] [(Term.typeSpec ":" `Point)]) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "1") "," (num "2") ","] "⟩") (Termination.suffix [] []) []) []))"#,
    },
    // A `⟨…⟩` pattern before a do-`let`'s `|` fallback: the fallback scanner
    // (`matching/fallback.rs`) must count `⟨` as an opener, or `⟩` underflows its depth and
    // the alternative is refused at the `|`.
    Accepted {
        source: "def f (p : Option P) : Option Nat := do\n  let some ⟨a, b⟩ := p | none\n  pure (a + b)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" (Term.app `Option [`P])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetElse "let" [] (Term.letConfig []) (Term.app `some [(Term.anonymousCtor "⟨" [`a "," `b] "⟩")]) ":=" `p "|" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `none) [])]) [(Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `a "+" `b) ")")])) [])])]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def k : List Point := [⟨1, 2⟩, ⟨3, 4⟩]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `k []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `List [`Point]))]) (Command.declValSimple ":=" («term[_]» "[" [(Term.anonymousCtor "⟨" [(num "1") "," (num "2")] "⟩") "," (Term.anonymousCtor "⟨" [(num "3") "," (num "4")] "⟩")] "]") (Termination.suffix [] []) []) []))"#,
    },
];

/// `.c`: `Term.dotIdent`, `"." >> checkNoWsBefore >> rawIdent` (`Lean/Parser/Term.lean:924`),
/// as a value, an application head, an argument, a `fun` body, a list element, and with a
/// dotted name (which the parser takes whole and the elaborator refuses as non-atomic). The
/// rows were captured after `inductive T where | leaf | node (l r : T)`, and the `theorem`
/// row is the last line of the stage-2 target I04 (`(T.node .leaf .leaf).size`).
const NUMERIC_PROJECTIONS: &[Accepted] = &[
    Accepted {
        source: "theorem a (p q : Prop) (h : p ∧ q) : q := h.2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `a []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" `q)] [] ")")] (Term.typeSpec ":" `q)) (Command.declValSimple ":=" (Term.proj `h "." (fieldIdx "2")) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b (p q r : Prop) (h : p ∧ q ∧ r) : q := h.2.1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b []) (Command.declSig [(Term.explicitBinder "(" [`p `q `r] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" («term_∧_» `q "∧" `r))] [] ")")] (Term.typeSpec ":" `q)) (Command.declValSimple ":=" (Term.proj (Term.proj `h "." (fieldIdx "2")) "." (fieldIdx "1")) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" `q)] [] ")")] (Term.typeSpec ":" («term_∧_» `q "∧" `p))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.proj `h "." (fieldIdx "2")) "," (Term.proj `h "." (fieldIdx "1"))] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// `h ▸ e`, right-nested.
const SUBSTITUTIONS: &[Accepted] = &[
    Accepted {
        source: "theorem a (x y z : Nat) (h1 : x = y) (h2 : y = z) : x = z := h1 ▸ h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `a []) (Command.declSig [(Term.explicitBinder "(" [`x `y `z] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `x "=" `y)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `y "=" `z)] [] ")")] (Term.typeSpec ":" («term_=_» `x "=" `z))) (Command.declValSimple ":=" (Term.subst `h1 "▸" [`h2]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b (x y z : Nat) (h1 : x = y) (h2 : y = z) (h : x = 0) : z = 0 := h2 ▸ h1 ▸ h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b []) (Command.declSig [(Term.explicitBinder "(" [`x `y `z] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `x "=" `y)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `y "=" `z)] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `x "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» `z "=" (num "0")))) (Command.declValSimple ":=" (Term.subst `h2 "▸" [(Term.subst `h1 "▸" [`h])]) (Termination.suffix [] []) [])))"#,
    },
];

/// `a |> f`, nested to the left.
const PIPE_RIGHT: &[Accepted] = &[
    Accepted {
        source: "def q1 (f : Nat → Nat) (a : Nat) : Nat := a |> f",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `q1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_|>_» `a "|>" `f) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def q2 (f g : Nat → Nat) (a : Nat) : Nat := a |> f |> g",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `q2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f `g] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_|>_» («term_|>_» `a "|>" `f) "|>" `g) (Termination.suffix [] []) []) []))"#,
    },
];

/// `inferInstanceAs` and its argument (the `<|` form is refused).
const INFER_INSTANCE_AS: &[Accepted] = &[
    Accepted {
        source: "def ia1 : Inhabited Nat := inferInstanceAs (Inhabited Nat)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ia1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Inhabited [`Nat]))]) (Command.declValSimple ":=" (Term.inferInstanceAs "inferInstanceAs" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Inhabited [`Nat]) ")")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "instance ia3 [OfNat α n] : OfNat (Id α) n :=\n  inferInstanceAs (OfNat α n)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [(Command.declId `ia3 [])] (Command.declSig [(Term.instBinder "[" [] (Term.app `OfNat [`α `n]) "]")] (Term.typeSpec ":" (Term.app `OfNat [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Id [`α]) ")") `n]))) (Command.declValSimple ":=" (Term.inferInstanceAs "inferInstanceAs" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `OfNat [`α `n]) ")")) (Termination.suffix [] []) [])))"#,
    },
];

/// `opaque`: a required signature and an optional `declValSimple`.
const OPAQUES: &[Accepted] = &[
    Accepted {
        source: "opaque O1 : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.opaque "opaque" (Command.declId `O1 []) (Command.declSig [] (Term.typeSpec ":" `Nat)) []))"#,
    },
    Accepted {
        source: "opaque O2 (n : Nat) : Nat := n + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.opaque "opaque" (Command.declId `O2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" `Nat)) [(Command.declValSimple ":=" («term_+_» `n "+" (num "1")) (Termination.suffix [] []) [])]))"#,
    },
    Accepted {
        source: "@[extern \"lean_o3\"] opaque O3 : Nat → Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.extern "extern" [(Attr.externEntry [] [] (str "\"lean_o3\""))]))] "]")] [] [] [] [] []) (Command.opaque "opaque" (Command.declId `O3 []) (Command.declSig [] (Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))) []))"#,
    },
];

/// `abbrev`: a definition's parts without its `deriving` slot.
const ABBREVIATIONS: &[Accepted] = &[
    Accepted {
        source: "abbrev A1 := Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.abbrev "abbrev" (Command.declId `A1 []) (Command.optDeclSig [] []) (Command.declValSimple ":=" `Nat (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "abbrev A2 (n : Nat) : Nat := n + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.abbrev "abbrev" (Command.declId `A2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» `n "+" (num "1")) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[reducible] abbrev A3 : Type := Nat × Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))] "]")] [] [] [] [] []) (Command.abbrev "abbrev" (Command.declId `A3 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.type "Type" []))]) (Command.declValSimple ":=" («term_×_» `Nat "×" `Nat) (Termination.suffix [] []) [])))"#,
    },
];

/// A typed `have` inside a match alternative, whose `:` belongs to the `have`, and `intros`.
const LOCALS_IN_ALTERNATIVES: &[Accepted] = &[
    Accepted {
        source: "def m1 (a : Nat) (h : True) : True :=\n  match a with\n  | 0 =>\n    have k : True := h\n    k\n  | _ => h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `m1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" `True] [] ")")] [(Term.typeSpec ":" `True)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.have "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `k) [] [(Term.typeSpec ":" `True)] ":=" `h)) [] `k)) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `h)])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def m3 (a : Nat) (h : True) : True :=\n  match a with\n  | 0 => have k : True := h; k\n  | _ => h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `m3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" `True] [] ")")] [(Term.typeSpec ":" `True)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.have "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `k) [] [(Term.typeSpec ":" `True)] ":=" `h)) ";" `k)) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" `h)])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem i1 : ∀ a b : Nat, a = a := by intros; rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `i1 []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [`a `b] [(Term.typeSpec ":" `Nat)] "," («term_=_» `a "=" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intros "intros" []) ";" (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem i2 : ∀ a b : Nat, a = a := by intros a _; rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `i2 []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [`a `b] [(Term.typeSpec ":" `Nat)] "," («term_=_» `a "=" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intros "intros" [`a (Term.hole "_")]) ";" (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `where` and structure fields as any declaration's value, not only an instance's.
const DECLARATION_WHERE: &[Accepted] = &[
    Accepted {
        source: "def w1 (a : Prop) : Inhabited (Decidable a) where\n  default := Classical.propDecidable a",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `w1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a] [":" (Term.prop "Prop")] [] ")")] [(Term.typeSpec ":" (Term.app `Inhabited [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Decidable [`a]) ")")]))]) (Command.whereStructInst "where" (Term.structInstFields [(Term.structInstField (Term.structInstLVal `default []) [[] [] (Term.structInstFieldDef ":=" [] (Term.app `Classical.propDecidable [`a]))])]) []) []))"#,
    },
    Accepted {
        source: "theorem w2 (p q : Prop) (hp : p) (hq : q) : p ∧ q where\n  left := hp\n  right := hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w2 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.whereStructInst "where" (Term.structInstFields [(Term.structInstField (Term.structInstLVal `left []) [[] [] (Term.structInstFieldDef ":=" [] `hp)]) [] (Term.structInstField (Term.structInstLVal `right []) [[] [] (Term.structInstFieldDef ":=" [] `hq)])]) [])))"#,
    },
];

/// Binder predicates: one name, an operator from `Init/BinderPredicates.lean`, its term.
const BINDER_PREDICATES: &[Accepted] = &[
    Accepted {
        source: "theorem q1 (xs : List Nat) (h : ∀ a ∈ xs, a = a) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q1 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`h] [":" (Lean.«term∀__,_» "∀" (Lean.binderIdent `a) (Lean.«binderPred∈_» "∈" `xs) "," («term_=_» `a "=" `a))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q2 (xs : List Nat) (h : ∃ a ∈ xs, a = 0) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q2 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`h] [":" (Lean.«term∃__,_» "∃" (Lean.binderIdent `a) (Lean.«binderPred∈_» "∈" `xs) "," («term_=_» `a "=" (num "0")))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q3 (h : ∀ n < 5, n ≠ 7) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q3 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" (Lean.«term∀__,_» "∀" (Lean.binderIdent `n) (Lean.«binderPred<_» "<" (num "5")) "," («term_≠_» `n "≠" (num "7")))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q4 (h : ∃ n ≥ 5, n = 7) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q4 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" (Lean.«term∃__,_» "∃" (Lean.binderIdent `n) (Lean.«binderPred≥_» "≥" (num "5")) "," («term_=_» `n "=" (num "7")))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q5 (xs : List Nat) (h : ∀ _ ∉ xs, True) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q5 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`h] [":" (Lean.«term∀__,_» "∀" (Lean.binderIdent (Term.hole "_")) (Lean.«binderPred∉_» "∉" `xs) "," `True)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q6 (h : ∀ n > 0, ∀ m ≤ n, m ≠ n + 1) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q6 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" (Lean.«term∀__,_» "∀" (Lean.binderIdent `n) (Lean.«binderPred>_» ">" (num "0")) "," (Lean.«term∀__,_» "∀" (Lean.binderIdent `m) (Lean.«binderPred≤_» "≤" `n) "," («term_≠_» `m "≠" («term_+_» `n "+" (num "1")))))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q7 (h : ∃ n ≠ 0, n = 1) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q7 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" (Lean.«term∃__,_» "∃" (Lean.binderIdent `n) (Lean.«binderPred≠_» "≠" (num "0")) "," («term_=_» `n "=" (num "1")))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
];

/// An explicit binder's default: a term, or a proof as the `by` block's own parts.
const BINDER_DEFAULTS: &[Accepted] = &[
    Accepted {
        source: "def r1 (start size : Nat) (step : Nat := 1) : Nat := start + size * step",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `r1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`start `size] [":" `Nat] [] ")") (Term.explicitBinder "(" [`step] [":" `Nat] [(Term.binderDefault ":=" (num "1"))] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» `start "+" («term_*_» `size "*" `step)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def r2 (n : Nat) (h : n = n := by rfl) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `r2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `n "=" `n)] [(Term.binderTactic ":=" "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def r3 (f : Nat → Nat := fun x => x + 1) (a : Nat := 0) : Nat := f a",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `r3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [(Term.binderDefault ":=" (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_+_» `x "+" (num "1")))))] ")") (Term.explicitBinder "(" [`a] [":" `Nat] [(Term.binderDefault ":=" (num "0"))] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `f [`a]) (Termination.suffix [] []) []) []))"#,
    },
];

/// A declaration binder named by a hole (`binderIdent`).
const HOLE_BINDERS: &[Accepted] = &[
    Accepted {
        source: "theorem b1 {_ : Decidable True} (t e : Nat) : ite True t e = t := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b1 []) (Command.declSig [(Term.implicitBinder "{" [(Term.hole "_")] [":" (Term.app `Decidable [`True])] "}") (Term.explicitBinder "(" [`t `e] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `ite [`True `t `e]) "=" `t))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b2 (_ : Nat) (n : Nat) : n = n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b2 []) (Command.declSig [(Term.explicitBinder "(" [(Term.hole "_")] [":" `Nat] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b3 (_ _ : Nat) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b3 []) (Command.declSig [(Term.explicitBinder "(" [(Term.hole "_") (Term.hole "_")] [":" `Nat] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
];

/// An anonymous `letI` inside a statement (whose `:=` is not the declaration's), `@& T`, and
/// the ellipsis argument `f ..`.
const LOCAL_INSTANCES_BORROWS_ELLIPSES: &[Accepted] = &[
    Accepted {
        source: "theorem z1 {n : Nat} (hn : n > 0) : letI : Inhabited Nat := ⟨n⟩; (default : Nat) = n := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `z1 []) (Command.declSig [(Term.implicitBinder "{" [`n] [":" `Nat] "}") (Term.explicitBinder "(" [`hn] [":" («term_>_» `n ">" (num "0"))] [] ")")] (Term.typeSpec ":" (Term.letI "letI" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [(Term.typeSpec ":" (Term.app `Inhabited [`Nat]))] ":=" (Term.anonymousCtor "⟨" [`n] "⟩"))) ";" («term_=_» (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `default ":" [`Nat] ")") "=" `n)))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def z2 (x : @& Nat) : Nat := x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `z2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" (Term.borrowed "@&" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `x (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem z5 (a b : Nat) (h : a = b) : b = a := Eq.symm ..",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `z5 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.app `Eq.symm [(Term.ellipsis "..")]) (Termination.suffix [] []) [])))"#,
    },
];

/// `cases`/`induction` `using` an eliminator, alternatives sharing a body (`| zero | succ m =>`)
/// or without one (`| succ m ih`, the sequence goes on), `rename_i`, `next`, `trivial`, and
/// `by_cases` under the pin's root kind (`«tacticBy_cases_:_»`, `Init/ByCases.lean`).
const MORE_TACTICS: &[Accepted] = &[
    Accepted {
        source: "theorem w1 (n : Nat) : n = n := by\n  induction n using Nat.strongRecOn with | ind n ih\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] ["using" `Nat.strongRecOn] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `ind) [`n `ih])] [])])]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem w3 (n : Nat) : n = n := by\n  cases n with | zero => rfl | succ m\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `succ) [`m])] [])])]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem w4 (n : Nat) : n = n := by\n  cases n with\n  | zero | succ m => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) []) (Tactic.inductionAltLHS "|" (group [] `succ) [`m])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem w5 (n : Nat) : n = n := by\n  induction n with\n  | zero => rfl\n  | succ m ih\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w5 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] [] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `succ) [`m `ih])] [])])]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem w6 (n : Nat) : n = n := by\n  cases n with\n  | zero | succ m\n  all_goals rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w6 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) []) (Tactic.inductionAltLHS "|" (group [] `succ) [`m])] [])])]) [] (Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u1 (n : Nat) : n = n := by\n  induction n using Nat.strongRecOn with\n  | ind n ih => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] ["using" `Nat.strongRecOn] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `ind) [`n `ih])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u2 (n : Nat) : n = n := by\n  cases n using Nat.casesAuxOn <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `n)] ["using" `Nat.casesAuxOn] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem r1 (p : Prop) [Decidable p] : True := by\n  by_cases p\n  · rename_i h\n    trivial\n  · next hp => trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r1 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.instBinder "[" [] (Term.app `Decidable [`p]) "]")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(«tacticBy_cases_:_» "by_cases" [] `p) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.renameI "rename_i" [(Lean.binderIdent `h)]) [] (Tactic.tacticTrivial "trivial")]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tacticNext_=>_» "next" [(Lean.binderIdent `hp)] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")])))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem r2 : ∀ a b : Nat, a = a := by\n  intros\n  rename_i x y\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r2 []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [`a `b] [(Term.typeSpec ":" `Nat)] "," («term_=_» `a "=" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intros "intros" []) [] (Tactic.renameI "rename_i" [(Lean.binderIdent `x) (Lean.binderIdent `y)]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem r3 : True := by\n  next => trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r3 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tacticNext_=>_» "next" [] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c1 (p : Prop) [Decidable p] : True := by\n  by_cases p <;> exact True.intro",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c1 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.instBinder "[" [] (Term.app `Decidable [`p]) "]")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» («tacticBy_cases_:_» "by_cases" [] `p) "<;>" (Tactic.exact "exact" `True.intro))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c2 (p : Prop) [Decidable p] : True := by\n  by_cases h : p <;> exact True.intro",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c2 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.instBinder "[" [] (Term.app `Decidable [`p]) "]")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» («tacticBy_cases_:_» "by_cases" [`h ":"] `p) "<;>" (Tactic.exact "exact" `True.intro))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c3 : True := by trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c3 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `obtain`, `rcases` and `rintro` with tuple, alternative, clear, ignore, parenthesized and
/// typed patterns.
const RCASES: &[Accepted] = &[
    Accepted {
        source: "theorem o1 (h : ∃ n : Nat, n = 0) : True := by\n  obtain ⟨n, hn⟩ := h\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o1 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" `Nat])) "," («term_=_» `n "=" (num "0")))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.obtain "obtain" [(Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])] "⟩")])] [] [":=" [`h]]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem o2 (p q : Prop) (h : p ∨ q) : True := by\n  rcases h with hp | hq\n  · trivial\n  · trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o2 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∨_» `p "∨" `q)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rcases "rcases" [(Tactic.elimTarget [] `h)] ["with" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hp) "|" (Tactic.rcasesPat.one `hq)]) [])]) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem o3 (p q : Prop) : p ∧ q → True := by\n  rintro ⟨hp, -⟩\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o3 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow («term_∧_» `p "∧" `q) "→" `True))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rintro "rintro" [(Tactic.rintroPat.one (Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hp)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])] "⟩"))] []) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem o4 (h : ∃ n : Nat, n = 0 ∧ True) : True := by\n  rcases h with ⟨n, rfl, _⟩\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o4 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" `Nat])) "," («term_∧_» («term_=_» `n "=" (num "0")) "∧" `True))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rcases "rcases" [(Tactic.elimTarget [] `h)] ["with" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])] "⟩")]) [])]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem o5 (p q : Prop) : p ∧ q → q ∧ p := by\n  rintro ⟨hp, hq⟩\n  exact ⟨hq, hp⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o5 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow («term_∧_» `p "∧" `q) "→" («term_∧_» `q "∧" `p)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rintro "rintro" [(Tactic.rintroPat.one (Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hp)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hq)]) [])] "⟩"))] []) [] (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`hq "," `hp] "⟩"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem p1 (h : ∃ n : Nat, n = 0 ∧ True) : True := by\n  rcases h with ⟨_, _ | _, -⟩ <;> trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `p1 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" `Nat])) "," («term_∧_» («term_=_» `n "=" (num "0")) "∧" `True))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.rcases "rcases" [(Tactic.elimTarget [] `h)] ["with" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_") "|" (Tactic.rcasesPat.ignore "_")]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])] "⟩")]) [])]) "<;>" (Tactic.tacticTrivial "trivial"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem p2 (p q : Prop) (h : p ∧ q) : True := by\n  obtain ⟨hp, hq⟩ : p ∧ q := h\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `p2 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" `q)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.obtain "obtain" [(Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hp)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hq)]) [])] "⟩")])] [":" («term_∧_» `p "∧" `q)] [":=" [`h]]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem p3 (p q : Prop) (h : p ∧ q) : True := by\n  rcases h with (⟨hp, hq⟩ : p ∧ q)\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `p3 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" `q)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rcases "rcases" [(Tactic.elimTarget [] `h)] ["with" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.paren "(" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hp)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hq)]) [])] "⟩")]) [":" («term_∧_» `p "∧" `q)]) ")")]) [])]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `replace`, `congr`, `funext`, `ext`, `dsimp`, tactic and term `suffices` (named, anonymous,
/// `from` and `by`), `case`/`case'` with tags and names, and the goal markers `⊢` and `|-`
/// (`patternIgnore`, the latter a `group` of `|` and `-`).
const SUFFICES_CASES_AND_GOALS: &[Accepted] = &[
    Accepted {
        source: "theorem e1 (p : Prop) (h : p) : p := by\n  replace h : p := h\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `e1 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.replace "replace" (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" `p)] ":=" `h))) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem e3 (a b : Nat) (h : a = b) : a + 1 = b + 1 := by\n  congr",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `e3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "1")) "=" («term_+_» `b "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem e4 (a b : Nat) (h : a = b) : a + 1 = b + 1 := by\n  congr 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `e4 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "1")) "=" («term_+_» `b "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [(num "1")])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f2 (f g : Nat → Nat → Nat) (h : ∀ x y, f x y = g x y) : f = g := by\n  funext x y\n  exact h x y",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f2 []) (Command.declSig [(Term.explicitBinder "(" [`f `g] [":" (Term.arrow `Nat "→" (Term.arrow `Nat "→" `Nat))] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`x `y] [] "," («term_=_» (Term.app `f [`x `y]) "=" (Term.app `g [`x `y])))] [] ")")] (Term.typeSpec ":" («term_=_» `f "=" `g))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticFunext___ "funext" [`x `y]) [] (Tactic.exact "exact" (Term.app `h [`x `y]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f1 (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by\n  ext x\n  exact h x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f1 []) (Command.declSig [(Term.explicitBinder "(" [`f `g] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`x] [] "," («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x])))] [] ")")] (Term.typeSpec ":" («term_=_» `f "=" `g))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.Elab.Tactic.Ext.ext "ext" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))] []) [] (Tactic.exact "exact" (Term.app `h [`x]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f7 (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by\n  ext\n  exact h _",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f7 []) (Command.declSig [(Term.explicitBinder "(" [`f `g] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`x] [] "," («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x])))] [] ")")] (Term.typeSpec ":" («term_=_» `f "=" `g))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.Elab.Tactic.Ext.ext "ext" [] []) [] (Tactic.exact "exact" (Term.app `h [(Term.hole "_")]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f3 (a : Nat) (h : a = 1) : a + 0 = 1 := by\n  dsimp\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f3 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.dsimp "dsimp" (Tactic.optConfig []) [] [] [] []) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f4 (a : Nat) (h : a = 1) : a + 0 = 1 := by\n  dsimp only [Nat.add_zero] at h ⊢\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f4 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.dsimp "dsimp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] `Nat.add_zero)] "]"] [(Tactic.location "at" (Tactic.locationHyp [`h (Tactic.locationType (patternIgnore (token.«⊢» "⊢")))]))]) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f5 (p q : Prop) (hp : p) (hpq : p → q) : q := by\n  suffices h : p by exact hpq h\n  exact hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f5 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hpq] [":" (Term.arrow `p "→" `q)] [] ")")] (Term.typeSpec ":" `q)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSuffices_ "suffices" (Term.sufficesDecl (group `h ":") `p (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.app `hpq [`h]))]))))) [] (Tactic.exact "exact" `hp)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f8 (p q : Prop) (hp : p) (hpq : p → q) : q := by\n  suffices p from hpq this\n  exact hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f8 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hpq] [":" (Term.arrow `p "→" `q)] [] ")")] (Term.typeSpec ":" `q)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSuffices_ "suffices" (Term.sufficesDecl (hygieneInfo `[anonymous]) `p (Term.fromTerm "from" (Term.app `hpq [`this])))) [] (Tactic.exact "exact" `hp)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g5 (a b : Nat) (h : a = b) : b = a := by\n  suffices b = b by\n    rw [h]\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g5 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSuffices_ "suffices" (Term.sufficesDecl (hygieneInfo `[anonymous]) («term_=_» `b "=" `b) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g1 (p q : Prop) (hp : p) (hpq : p → q) : q :=\n  suffices h : p from hpq h\n  hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g1 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hpq] [":" (Term.arrow `p "→" `q)] [] ")")] (Term.typeSpec ":" `q)) (Command.declValSimple ":=" (Term.suffices "suffices" (Term.sufficesDecl (group `h ":") `p (Term.fromTerm "from" (Term.app `hpq [`h]))) [] `hp) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem f6 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  case left => exact hp\n  case right => exact hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `f6 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `left) [])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) [] (Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `right) [])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq)])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g3 (p q : Prop) (h : p ∧ q) : q ∧ p := by\n  constructor\n  case' left => exact h.2\n  all_goals exact h.1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g3 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" `q)] [] ")")] (Term.typeSpec ":" («term_∧_» `q "∧" `p))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Tactic.case' "case'" [(Tactic.caseArg (Lean.binderIdent `left) [])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.proj `h "." (fieldIdx "2")))]))) [] (Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.proj `h "." (fieldIdx "1")))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g4 (n : Nat) : n + 0 = n := by\n  induction n\n  case zero => rfl\n  case succ m ih => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] [] [] []) [] (Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `zero) [])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) [] (Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `succ) [(Lean.binderIdent `m) (Lean.binderIdent `ih)])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem k1 (a b : Nat) (h : a = b) (h2 : a = 0) : b = 0 := by\n  rw [h] at h2 ⊢\n  exact h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `k1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `a "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [(Tactic.location "at" (Tactic.locationHyp [`h2 (Tactic.locationType (patternIgnore (token.«⊢» "⊢")))]))]) [] (Tactic.exact "exact" `h2)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem k2 (a b : Nat) (h : a = b) (h2 : a = 0) : b = 0 := by\n  rw [h] at h2 |-\n  exact h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `k2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `a "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [(Tactic.location "at" (Tactic.locationHyp [`h2 (Tactic.locationType (patternIgnore (group "|" "-")))]))]) [] (Tactic.exact "exact" `h2)]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `grind_pattern` with one and several patterns, `local`/`scoped`, and a bracketed name
/// (`Command.grindPattern`, `Lean/Meta/Tactic/Grind/Parser.lean`), with `where` constraints
/// (`=/=`, `guard`; `;` or a line between them). Also `export N (a b)` (`Command.export`),
/// another command the checker refuses.
const GRIND_PATTERNS: &[Accepted] = &[
    Accepted {
        source: "grind_pattern Nat.add_zero => n + 0",
        tree: r#"(Command.grindPattern (Term.attrKind []) "grind_pattern" [] `Nat.add_zero "=>" [(«term_+_» `n "+" (num "0"))] [])"#,
    },
    Accepted {
        source: "grind_pattern mem_pmap_of_mem => _ ∈ pmap f xs H, a ∈ xs",
        tree: r#"(Command.grindPattern (Term.attrKind []) "grind_pattern" [] `mem_pmap_of_mem "=>" [(«term_∈_» (Term.hole "_") "∈" (Term.app `pmap [`f `xs `H])) "," («term_∈_» `a "∈" `xs)] [])"#,
    },
    Accepted {
        source: "local grind_pattern Nat.zero_add => 0 + n",
        tree: r#"(Command.grindPattern (Term.attrKind [(Term.local "local")]) "grind_pattern" [] `Nat.zero_add "=>" [(«term_+_» (num "0") "+" `n)] [])"#,
    },
    Accepted {
        source: "scoped grind_pattern [ematch] Nat.mul_one => n * 1",
        tree: r#"(Command.grindPattern (Term.attrKind [(Term.scoped "scoped")]) "grind_pattern" ["[" `ematch "]"] `Nat.mul_one "=>" [(«term_*_» `n "*" (num "1"))] [])"#,
    },
    Accepted {
        source: "export Foo (bar baz)",
        tree: r#"(Command.export "export" `Foo "(" [`bar `baz] ")")"#,
    },
    Accepted {
        source: "grind_pattern append_assoc => (xs ++ ys) ++ zs where\n  xs =/= #[]; ys =/= #[]; zs =/= #[]",
        tree: r##"(Command.grindPattern (Term.attrKind []) "grind_pattern" [] `append_assoc "=>" [(«term_++_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_++_» `xs "++" `ys) ")") "++" `zs)] [(Command.grindPatternCnstrs "where" [(Command.GrindCnstr.notDefEq `xs "=/=" («term#[_,]» "#[" [] "]") [";"]) (Command.GrindCnstr.notDefEq `ys "=/=" («term#[_,]» "#[" [] "]") [";"]) (Command.GrindCnstr.notDefEq `zs "=/=" («term#[_,]» "#[" [] "]") [])])])"##,
    },
    Accepted {
        source: "grind_pattern fMono => f x, f y where\n  guard x ≤ y\n  x =/= y",
        tree: r#"(Command.grindPattern (Term.attrKind []) "grind_pattern" [] `fMono "=>" [(Term.app `f [`x]) "," (Term.app `f [`y])] [(Command.grindPatternCnstrs "where" [(Command.GrindCnstr.guard "guard" («term_≤_» `x "≤" `y) []) (Command.GrindCnstr.notDefEq `x "=/=" `y [])])])"#,
    },
];

/// `>>=` (left-nested), the `List` relations `<+:`, `<:+`, `<:+:` (kinds in namespace `List`),
/// and the prefixes `!` (operand at 40, so `!b && c` negates `b`; an argument too) and `~~~`
/// (operand at 100).
const BIND_LIST_RELATIONS_AND_PREFIXES: &[Accepted] = &[
    Accepted {
        source: "def b1 (x : Option Nat) (f : Nat → Option Nat) : Option Nat := x >>= f >>= f",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `b1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" (Term.app `Option [`Nat])] [] ")") (Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" (Term.app `Option [`Nat]))] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_>>=_» («term_>>=_» `x ">>=" `f) ">>=" `f) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem b2 (l₁ l₂ l₃ : List Nat) (h : l₁ <+: l₂) (g : l₂ <:+ l₃) (k : l₁ <:+: l₃) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b2 []) (Command.declSig [(Term.explicitBinder "(" [`l₁ `l₂ `l₃] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`h] [":" (List.«term_<+:_» `l₁ "<+:" `l₂)] [] ")") (Term.explicitBinder "(" [`g] [":" (List.«term_<:+_» `l₂ "<:+" `l₃)] [] ")") (Term.explicitBinder "(" [`k] [":" (List.«term_<:+:_» `l₁ "<:+:" `l₃)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b3 (a b : List Nat) : (a <+: a ++ b) = (a <+: a ++ b) := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" (Term.app `List [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (List.«term_<+:_» `a "<+:" («term_++_» `a "++" `b)) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (List.«term_<+:_» `a "<+:" («term_++_» `a "++" `b)) ")")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def p1 (b c : Bool) : Bool := !b && c",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`b `c] [":" `Bool] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" («term_&&_» (term!_ "!" `b) "&&" `c) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def p2 (b : Bool) (l : List Bool) : Bool := !l.contains b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")") (Term.explicitBinder "(" [`l] [":" (Term.app `List [`Bool])] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" (term!_ "!" (Term.app `l.contains [`b])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def p3 (a b : UInt8) : UInt8 := ~~~a &&& b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `UInt8] [] ")")] [(Term.typeSpec ":" `UInt8)]) (Command.declValSimple ":=" («term_&&&_» («term~~~_» "~~~" `a) "&&&" `b) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def p4 (f : Bool → Bool) (b : Bool) : Bool := f !b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Bool "→" `Bool)] [] ")") (Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" (Term.app `f [(term!_ "!" `b)]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def p5 (a : UInt8) : UInt8 := ~~~a + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a] [":" `UInt8] [] ")")] [(Term.typeSpec ":" `UInt8)]) (Command.declValSimple ":=" («term_+_» («term~~~_» "~~~" `a) "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
];

/// `inferInstanceAs <| T` (the keyword's own `<|` slot, nested pipelines to its right), `bif c then
/// a else b` (`boolIfThenElse`, nested and parenthesized), and `xs[i]'h` with a name or a
/// parenthesized proof (`term__[_]'_`).
const INSTANCE_PIPES_BOOL_CONDITIONALS_AND_PROVED_INDICES: &[Accepted] = &[
    Accepted {
        source: "instance i1 : Inhabited Nat := inferInstanceAs <| Inhabited Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [(Command.declId `i1 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.inferInstanceAs "inferInstanceAs" "<|" (Term.app `Inhabited [`Nat])) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "instance i2 : Inhabited Nat := inferInstanceAs (Inhabited Nat)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [(Command.declId `i2 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.inferInstanceAs "inferInstanceAs" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Inhabited [`Nat]) ")")) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def q1 (b : Bool) (x y : Nat) : Nat := bif b then x else y",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `q1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")") (Term.explicitBinder "(" [`x `y] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (boolIfThenElse "bif" `b "then" `x "else" `y) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem q2 (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i]'h = xs[i]'h := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q2 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» `i "<" `xs.size)] [] ")")] (Term.typeSpec ":" («term_=_» («term__[_]'_» `xs "[" `i "]'" `h) "=" («term__[_]'_» `xs "[" `i "]'" `h)))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q3 (xs : Array Nat) (i : Nat) (h : i + 1 < xs.size) : xs[i]'(by omega) = xs[i]'(by omega) := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q3 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» («term_+_» `i "+" (num "1")) "<" `xs.size)] [] ")")] (Term.typeSpec ":" («term_=_» («term__[_]'_» `xs "[" `i "]'" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) ")")) "=" («term__[_]'_» `xs "[" `i "]'" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) ")"))))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def q4 (b c : Bool) (x y : Nat) : Nat := bif b && c then x + 1 else bif c then y else 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `q4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`b `c] [":" `Bool] [] ")") (Term.explicitBinder "(" [`x `y] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (boolIfThenElse "bif" («term_&&_» `b "&&" `c) "then" («term_+_» `x "+" (num "1")) "else" (boolIfThenElse "bif" `c "then" `y "else" (num "0"))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def q5 (b : Bool) (x : Nat) : Nat := (bif b then x else 0) + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `q5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")") (Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (boolIfThenElse "bif" `b "then" `x "else" (num "0")) ")") "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "instance i3 : Inhabited Nat := inferInstanceAs <| Inhabited <| Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [(Command.declId `i3 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.inferInstanceAs "inferInstanceAs" "<|" («term_<|_» `Inhabited "<|" `Nat)) (Termination.suffix [] []) [])))"#,
    },
];

/// `e |>.f args` (`Term.pipeProj`): a field, a method with arguments, a left-nested chain, after
/// an application, and a positional field (`fieldIdx`).
const PIPELINE_PROJECTIONS: &[Accepted] = &[
    Accepted {
        source: "def r1 (l : List Nat) : Nat := l |>.length",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `r1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.pipeProj `l "|>." `length [] []) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def r2 (l : List Nat) (f : Nat → Nat) : List Nat := l |>.map f |>.reverse",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `r2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.pipeProj (Term.pipeProj `l "|>." `map [] [`f]) "|>." `reverse [] []) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def r3 (l : List Nat) : Nat := l.map (· + 1) |>.foldl (· + ·) 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `r3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.pipeProj (Term.app `l.map [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.cdot "·" (hygieneInfo `[anonymous])) "+" (num "1")) ")")]) "|>." `foldl [] [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.cdot "·" (hygieneInfo `[anonymous])) "+" (Term.cdot "·" (hygieneInfo `[anonymous]))) ")") (num "0")]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem r4 (p q : Prop) (h : p ↔ q) (hp : p) : q := h |>.mp hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r4 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_↔_» `p "↔" `q)] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")")] (Term.typeSpec ":" `q)) (Command.declValSimple ":=" (Term.pipeProj `h "|>." `mp [] [`hp]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def r5 (x : Nat × Nat) : Nat := x |>.1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `r5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.pipeProj `x "|>." (fieldIdx "1") [] []) (Termination.suffix [] []) []) []))"#,
    },
];

/// An explicit binder's default with no type (`(x := v)`), configuration flags (`+x`, `-x`) on
/// `decide`, `simp` and `omega`, and lambda binders that are anonymous-constructor patterns.
const DEFAULTS_FLAGS_AND_PATTERN_BINDERS: &[Accepted] = &[
    Accepted {
        source: "def s1 (x : Nat) (useFirst := true) : Nat := if useFirst then x else 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `s1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")") (Term.explicitBinder "(" [`useFirst] [] [(Term.binderDefault ":=" `true)] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfThenElse "if" `useFirst "then" `x "else" (num "0")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def s2 (f : Nat → Nat := id) (n : Nat) : Nat := f n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `s2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [(Term.binderDefault ":=" `id)] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `f [`n]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem s3 : True := by decide +revert",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s3 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig [(Tactic.configItem (Tactic.posConfigItem "+" `revert))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem s4 (a : Nat) : a + 0 = a := by simp +arith",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s4 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig [(Tactic.configItem (Tactic.posConfigItem "+" `arith))]) [] [] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem s5 : 2 + 2 = 4 := by decide +kernel",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s5 []) (Command.declSig [] (Term.typeSpec ":" («term_=_» («term_+_» (num "2") "+" (num "2")) "=" (num "4")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig [(Tactic.configItem (Tactic.posConfigItem "+" `kernel))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def s6 : Nat × Nat → Nat := fun ⟨x, _⟩ => x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `s6 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow («term_×_» `Nat "×" `Nat) "→" `Nat))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.anonymousCtor "⟨" [`x "," (Term.hole "_")] "⟩")] [] "=>" `x)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def s7 (f : Nat → Nat) : Nat → Nat := fun\n  | 0 => f 0\n  | n + 1 => f n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `s7 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")")] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.app `f [(num "0")])) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" (Term.app `f [`n]))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem s8 (a : Nat) (h : a = 1) : a + 0 = 1 := by simp -zeta +arith only [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s8 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig [(Tactic.configItem (Tactic.negConfigItem "-" `zeta)) (Tactic.configItem (Tactic.posConfigItem "+" `arith))]) [] ["only"] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem s9 : 3 < 5 := by omega -splitDisjunctions",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s9 []) (Command.declSig [] (Term.typeSpec ":" («term_<_» (num "3") "<" (num "5")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig [(Tactic.configItem (Tactic.negConfigItem "-" `splitDisjunctions))]))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `⊕` and `•` (right-nested), `specialize`, tactic `letI`/`haveI`, `subst` with several names,
/// `grind` with flags only, and `no_index e`.
const SUMS_SCALARS_AND_MORE_TACTICS: &[Accepted] = &[
    Accepted {
        source: "def u1 (α β γ : Type) : Type := α ⊕ β ⊕ γ",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `u1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`α `β `γ] [":" (Term.type "Type" [])] [] ")")] [(Term.typeSpec ":" (Term.type "Type" []))]) (Command.declValSimple ":=" («term_⊕_» `α "⊕" («term_⊕_» `β "⊕" `γ)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def u2 (a : Nat) (v : Nat) : Nat := a • v + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `u2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`v] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» («term_•_» `a "•" `v) "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem u3 (p : Nat → Prop) (h : ∀ n, p n) : p 0 := by\n  specialize h 0\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u3 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.arrow `Nat "→" (Term.prop "Prop"))] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`n] [] "," (Term.app `p [`n]))] [] ")")] (Term.typeSpec ":" (Term.app `p [(num "0")]))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.specialize "specialize" (Term.app `h [(num "0")])) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u4 (n : Nat) : n = n := by\n  letI x := n\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticLetI__ "letI" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [] ":=" `n))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u5 (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by\n  subst h₁ h₂\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u5 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h₁] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h₂] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.subst "subst" [`h₁ `h₂]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u6 (a : Nat) : a = a := by grind",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u6 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig []) [] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u7 (f : Nat → Nat) (h : ∀ x, f x = x) : f (no_index (f 0)) = f 0 := by simp [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u7 []) (Command.declSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`x] [] "," («term_=_» (Term.app `f [`x]) "=" `x))] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.noindex "no_index" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `f [(num "0")]) ")")) ")")]) "=" (Term.app `f [(num "0")])))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u8 (n : Nat) : n = n := by\n  haveI h : n = n := rfl\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u8 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHaveI__ "haveI" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" («term_=_» `n "=" `n))] ":=" `rfl))) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u9 (a : Nat) : a = a := by grind +ring",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u9 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig [(Tactic.configItem (Tactic.posConfigItem "+" `ring))]) [] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A `match` anywhere in a result type takes the alternatives after it (they are not the
/// declaration's equations), a match in a value after an operator, and a `where` field defined
/// by equations (`structInstFieldEqns`).
const MATCHES_IN_TYPES_AND_FIELD_EQUATIONS: &[Accepted] = &[
    Accepted {
        source: "theorem w4 (a : Nat) : a = match a with | 0 => 0 | n + 1 => n + 1 := by cases a <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w4 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" (Term.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" («term_+_» `n "+" (num "1")))]))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `a)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def w5 (a : Nat) : Nat := 1 +\n  match a with\n  | 0 => 0\n  | _ => 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `w5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (num "1") "+" (Term.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" (num "1"))]))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem w6 (a : Nat) :\n    a = match a with\n      | 0 => 0\n      | n + 1 => n + 1 := by\n  cases a <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w6 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" (Term.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" («term_+_» `n "+" (num "1")))]))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `a)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def w7 (a : Nat) : Nat :=\n  match a with\n  | 0 => 0\n  | _ => 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `w7 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" (num "1"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "instance x1 : ToString Bool where\n  toString\n    | true => \"t\"\n    | false => \"f\"",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [(Command.declId `x1 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `ToString [`Bool]))) (Command.whereStructInst "where" (Term.structInstFields [(Term.structInstField (Term.structInstLVal `toString []) [[] [] (Term.structInstFieldEqns [] (Term.matchAlts [(Term.matchAlt "|" [[`true]] "=>" (str "\"t\"")) (Term.matchAlt "|" [[`false]] "=>" (str "\"f\""))]))])]) [])))"#,
    },
    Accepted {
        source: "theorem w1 (a : Nat) :\n    a + 0 =\n      match a with\n      | 0 => 0\n      | n + 1 => n + 1 := by\n  cases a <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w1 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" (Term.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" («term_+_» `n "+" (num "1")))]))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `a)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// The tactic `match` (one and two discriminants, a named one, a row whose body is on the next
/// line), a proof ascribed in its parenthesis (`(by tac : T)`), and proofs as anonymous-constructor
/// fields, which end at their comma.
const TACTIC_MATCHES_AND_ASCRIBED_PROOFS: &[Accepted] = &[
    Accepted {
        source: "theorem z1 (o : Option Nat) : o = o := by\n  match o with\n  | some _ => rfl\n  | none => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `z1 []) (Command.declSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» `o "=" `o))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [(Term.hole "_")])]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[`none]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem z2 (a b : Nat) : a + b = a + b := by\n  match a, b with\n  | 0, _ => rfl\n  | n + 1, m =>\n    simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `z2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `a "+" `b)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0") "," (Term.hole "_")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1")) "," `m]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem z3 (a b : Nat) : a + b = a + b := by\n  match a, b with\n  | 0, _ => rfl\n  | _, _ => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `z3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `a "+" `b)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0") "," (Term.hole "_")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[(Term.hole "_") "," (Term.hole "_")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem z4 (a : Nat) : a = a := by\n  match a with\n  | 0 => rfl\n  | n + 1 =>\n    rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `z4 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem z5 (a : Nat) : a = a := by\n  match h : a with\n  | 0 => rfl\n  | _ => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `z5 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [`h ":"] `a)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem y1 (a b : Nat) (h : a = b) : b = a := (by omega : b = a)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `y1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) ":" [(«term_=_» `b "=" `a)] ")") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem y2 (p : Prop) (hp : p) : p := (by have h : p := hp; exact h : p)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `y2 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" `p)] ":=" `hp))) ";" (Tactic.exact "exact" `h)]))) ":" [`p] ")") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem y3 (w v : Nat) : w ≤ v ∨ v < w := (by omega : w ≤ v ∨ v < w).elim (fun h => Or.inl h) (fun h => Or.inr h)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `y3 []) (Command.declSig [(Term.explicitBinder "(" [`w `v] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_∨_» («term_≤_» `w "≤" `v) "∨" («term_<_» `v "<" `w)))) (Command.declValSimple ":=" (Term.app (Term.proj (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) ":" [(«term_∨_» («term_≤_» `w "≤" `v) "∨" («term_<_» `v "<" `w))] ")") "." `elim) [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.app `Or.inl [`h]))) ")") (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.app `Or.inr [`h]))) ")")]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem y4 (p : Prop) (hp : p) : p := (by exact hp)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `y4 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) ")") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q1 (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨by exact hp, by exact hq⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q1 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) "," (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq)])))] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q2 (o : Option Nat) (p : Prop) (hp : p) : p ∧ o = o := ⟨by exact hp, by match o with | some _ => rfl | none => rfl⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q2 []) (Command.declSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")") (Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" («term_=_» `o "=" `o)))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) "," (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [(Term.hole "_")])]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[`none]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))])))] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// `fun_induction` (with `generalizing`, alternatives, and under `<;>`) and `fun_cases`
/// (`Tactic.funInduction`, `Tactic.funCases`). The function `fib` they name is not declared here:
/// the trees are syntax only.
const FUNCTIONAL_INDUCTION: &[Accepted] = &[
    Accepted {
        source: "theorem a1 (n : Nat) : fib n ≥ 0 := by\n  fun_induction fib n <;> simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `a1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_≥_» (Term.app `fib [`n]) "≥" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.funInduction "fun_induction" (Term.app `fib [`n]) [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem a2 (n : Nat) : fib n ≥ 0 := by\n  fun_induction fib n with\n  | case1 => simp\n  | case2 => simp\n  | case3 n ih1 ih2 => simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `a2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_≥_» (Term.app `fib [`n]) "≥" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.funInduction "fun_induction" (Term.app `fib [`n]) [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `case1) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `case2) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `case3) [`n `ih1 `ih2])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem a3 (n : Nat) : fib n ≥ 0 := by\n  fun_cases fib n <;> simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `a3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_≥_» (Term.app `fib [`n]) "≥" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.funCases "fun_cases" (Term.app `fib [`n]) []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem a4 (n m : Nat) : fib n ≥ 0 := by\n  fun_induction fib n generalizing m <;> simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `a4 []) (Command.declSig [(Term.explicitBinder "(" [`n `m] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_≥_» (Term.app `fib [`n]) "≥" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.funInduction "fun_induction" (Term.app `fib [`n]) ["generalizing" [`m]] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// The bounded ranges `a...<b`, `a...b`, `a...=b`, `a<...<b`, `a<...b`, `a<...=b`
/// (`Std.«term_...<_»` and so on, one name component each), the bound after the symbol a whole
/// term.
const BOUNDED_RANGES: &[Accepted] = &[
    Accepted {
        source: "def g1 (n : Nat) : List Nat := (0...<n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_...<_» (num "0") "...<" `n) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def g2 (n : Nat) : List Nat := (1<...=n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_<...=_» (num "1") "<...=" `n) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def g3 (a b : Nat) : List Nat := (a...=b + 1).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_...=_» `a "...=" («term_+_» `b "+" (num "1"))) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def g4 (a b : Nat) : List Nat := (a<...<b).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_<...<_» `a "<...<" `b) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def g5 (a b : Nat) : List Nat := (a...b).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_..._» `a "..." `b) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def g6 (a b : Nat) : List Nat := (a<...b).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g6 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_<..._» `a "<..." `b) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
];

/// The ASCII focus dot `. tac` (`Lean.cdotTk "."`), the postfix `x⁻¹` (`«term_⁻¹»`), and
/// `simpa using! e` (`simpaUsingBang`, its `"using!" term` inline), and a tactic `have` whose
/// value holds a proof (`f (by omega)`), `where` declarations defined by equations
/// (`letEqnsDecl`), a tuple lambda binder (`fun (a, b) =>`), an anonymous tactic `letI`, and the
/// BitVec literal `5#w` (`BitVec.«term__#__»`), `panic! msg` (`Term.panic`), and `return e`
/// outside `do` (`Term.termReturn`), and `‹T›` (`«term‹_›»`).
const ASCII_FOCUS_AND_INVERSE: &[Accepted] = &[
    Accepted {
        source: "theorem h1 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  . exact hp\n  . exact hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h1 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Lean.cdot (Lean.cdotTk ".") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) [] (Lean.cdot (Lean.cdotTk ".") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq)])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def h2 (x : Nat) : Nat := x⁻¹ + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `h2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» («term_⁻¹» `x "⁻¹") "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem k1 (p : Prop) (h : p) : p := by\n  simpa using! h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `k1 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simpaUsingBang "simpa" [] [] (Tactic.simpaUsingBangArgsRest (Tactic.optConfig []) [] [] [] "using!" `h))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem m1 (n : Nat) (h : 0 < n) : n ≠ 0 := by\n  have h2 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (by omega)\n  exact h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `m1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» (num "0") "<" `n)] [] ")")] (Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h2) [] [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))] ":=" (Term.app `Nat.pos_iff_ne_zero.mp [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) ")")])))) [] (Tactic.exact "exact" `h2)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem m2 (a b : Nat) : a + b = b + a := by\n  have := Nat.add_comm a (by exact b)\n  exact this",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `m2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `b "+" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [] ":=" (Term.app `Nat.add_comm [`a (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `b)]))) ")")])))) [] (Tactic.exact "exact" `this)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def w1 (n : Nat) : Nat := go n\n  where\n  go : Nat → Nat\n    | 0 => 0\n    | k + 1 => go k",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `w1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `go [`n]) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letEqnsDecl (Term.letId `go) [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))] (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `k "+" (num "1"))]] "=>" (Term.app `go [`k]))]))) (Termination.suffix [] []))] [])]) []))"#,
    },
    Accepted {
        source: "def w2 (n : Nat) : Nat := go 0 n\n  where\n  go (acc : Nat) : Nat → Nat\n    | 0 => acc\n    | k + 1 => go (acc + 1) k",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `w2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `go [(num "0") `n]) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letEqnsDecl (Term.letId `go) [(Term.explicitBinder "(" [`acc] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))] (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" `acc) (Term.matchAlt "|" [[(«term_+_» `k "+" (num "1"))]] "=>" (Term.app `go [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `acc "+" (num "1")) ")") `k]))]))) (Termination.suffix [] []))] [])]) []))"#,
    },
    Accepted {
        source: "def b2 : Nat × Nat → Nat := fun (a, b) => a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `b2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow («term_×_» `Nat "×" `Nat) "→" `Nat))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")")] [] "=>" («term_+_» `a "+" `b))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem b3 (n : Nat) : n = n := by\n  letI : Inhabited Nat := ⟨0⟩\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticLetI__ "letI" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [(Term.typeSpec ":" (Term.app `Inhabited [`Nat]))] ":=" (Term.anonymousCtor "⟨" [(num "0")] "⟩")))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def bv1 (w : Nat) : BitVec w := 0#w",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bv1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`w] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `BitVec [`w]))]) (Command.declValSimple ":=" (BitVec.«term__#__» (num "0") "#" `w) (Termination.suffix [] []) []) []))"##,
    },
    Accepted {
        source: "def bv2 : BitVec 8 := 5#8 + 1#8",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bv2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `BitVec [(num "8")]))]) (Command.declValSimple ":=" («term_+_» (BitVec.«term__#__» (num "5") "#" (num "8")) "+" (BitVec.«term__#__» (num "1") "#" (num "8"))) (Termination.suffix [] []) []) []))"##,
    },
    Accepted {
        source: "def pn1 (n : Nat) : Nat := if n = 0 then panic! \"zero\" else n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `pn1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" (Term.panic "panic!" (str "\"zero\"")) "else" `n) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def pn2 (s : String) : Nat := panic! (s ++ \"!\")",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `pn2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`s] [":" `String] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.panic "panic!" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_++_» `s "++" (str "\"!\"")) ")")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def rt1 (x : Option Nat) : Option (Option Nat) := return some 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `rt1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Option [`Nat]) ")")]))]) (Command.declValSimple ":=" (Term.termReturn "return" [(Term.app `some [(num "1")])]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def rt2 (x : Option Nat) : Option (Option Nat) := (return some (← x) : Option (Option Nat))",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `rt2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Option [`Nat]) ")")]))]) (Command.declValSimple ":=" (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.termReturn "return" [(Term.app `some [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.nestedAction "←" (Term.doExpr `x)) ")")])]) ":" [(Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Option [`Nat]) ")")])] ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem as1 (p : Prop) (h : p) : p := ‹p›",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `as1 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" («term‹_›» "‹" `p "›") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem as2 (p : Prop) (h : p) : p := ‹_›",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `as2 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" («term‹_›» "‹" (Term.hole "_") "›") (Termination.suffix [] []) [])))"#,
    },
];

/// Structure instances whose fields are separated by line breaks (an empty separator node, also
/// before a `}` on its own line), mixed with commas, nested, after `with`, with a value continued
/// on a deeper line, and inside an anonymous constructor. `structure P3`/`Q3` are not declared
/// here: the trees are syntax only.
const LINE_SEPARATED_FIELDS: &[Accepted] = &[
    Accepted {
        source: "def c1 : P3 := { x := 1, y := 2 }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c1 []) (Command.optDeclSig [] [(Term.typeSpec ":" `P3)]) (Command.declValSimple ":=" (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (num "1"))]) "," (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "2"))])]) (Term.optEllipsis []) [] "}") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def c2 : Q3 := {\n  p := { x := 1, y := 2 }\n  z := 3 }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c2 []) (Command.optDeclSig [] [(Term.typeSpec ":" `Q3)]) (Command.declValSimple ":=" (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `p []) [[] [] (Term.structInstFieldDef ":=" [] (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (num "1"))]) "," (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "2"))])]) (Term.optEllipsis []) [] "}"))]) [] (Term.structInstField (Term.structInstLVal `z []) [[] [] (Term.structInstFieldDef ":=" [] (num "3"))])]) (Term.optEllipsis []) [] "}") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def c3 (q : P3) : P3 := { q with\n  x := 5\n  y := 6 }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`q] [":" `P3] [] ")")] [(Term.typeSpec ":" `P3)]) (Command.declValSimple ":=" (Term.structInst "{" [[`q] "with"] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (num "5"))]) [] (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "6"))])]) (Term.optEllipsis []) [] "}") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def c5 : P3 := {\n  x := Nat.add\n    1 2\n  y := 2\n  }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c5 []) (Command.optDeclSig [] [(Term.typeSpec ":" `P3)]) (Command.declValSimple ":=" (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (Term.app `Nat.add [(num "1") (num "2")]))]) [] (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "2"))]) []]) (Term.optEllipsis []) [] "}") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def c6 : P3 × Nat := ⟨{\n  x := 1\n  y := 2\n  }, 3⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c6 []) (Command.optDeclSig [] [(Term.typeSpec ":" («term_×_» `P3 "×" `Nat))]) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (num "1"))]) [] (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "2"))]) []]) (Term.optEllipsis []) [] "}") "," (num "3")] "⟩") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def c7 : P3 := { x := 1,\n                 y := 2, }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c7 []) (Command.optDeclSig [] [(Term.typeSpec ":" `P3)]) (Command.declValSimple ":=" (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (num "1"))]) "," (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "2"))]) ","]) (Term.optEllipsis []) [] "}") (Termination.suffix [] []) []) []))"#,
    },
];

/// `termination_by` (a term, a tuple, `structural` with binders, after equations) and
/// `decreasing_by` (`Termination.suffix`).
const TERMINATION_CLAUSES: &[Accepted] = &[
    Accepted {
        source: "def t1 (n : Nat) : Nat := if n = 0 then 0 else t1 (n - 1)\n  termination_by n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `t1 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")])) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] []) []) []))"#,
    },
    Accepted {
        source: "def t2 (n : Nat) : Nat := if h : n = 0 then 0 else t2 (n - 1)\n  termination_by n\n  decreasing_by omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `t2 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")])) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))]) []) []))"#,
    },
    Accepted {
        source: "def t3 : Nat → Nat\n  | 0 => 0\n  | n + 1 => t3 n\n  termination_by structural n => n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t3 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" (Term.app `t3 [`n]))]) (Termination.suffix [(Termination.terminationBy "termination_by" ["structural"] [[`n] "=>"] `n)] []) [])) []))"#,
    },
    Accepted {
        source: "def t4 (n m : Nat) : Nat := if n = 0 then m else t4 (n - 1) m\n  termination_by (n, m)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n `m] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" `m "else" (Term.app `t4 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")") `m])) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`n "," [`m]] ")"))] []) []) []))"#,
    },
];

/// Tuple patterns in match rows, of two and three elements and nested in literals and holes
/// (`Term.tuple`, as the term); and compound brackets (`xs[i]'h`, `#[…]`) inside match rows.
const TUPLE_PATTERNS: &[Accepted] = &[
    Accepted {
        source: "def mt1 (p : Nat × Nat) : Nat := match p with\n  | (a, b) => a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `p)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")")]] "=>" («term_+_» `a "+" `b))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def mt2 (p : Nat × Nat × Nat) : Nat := match p with\n  | (a, b, c) => a + b + c",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" («term_×_» `Nat "×" `Nat))] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `p)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b "," `c]] ")")]] "=>" («term_+_» («term_+_» `a "+" `b) "+" `c))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def mt3 (p : Nat × Nat) : Nat := match p with\n  | (0, _) => 0\n  | (a, b) => a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `p)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(num "0") "," [(Term.hole "_")]] ")")]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")")]] "=>" («term_+_» `a "+" `b))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ei1 (xs ys : Array Nat) (hsz : xs.size = ys.size) : ∀ (i : Nat) (_ : i ≤ xs.size), Bool\n  | 0, _ => true\n  | i+1, h => xs[i] == ys[i]'(hsz ▸ h) && ei1 xs ys hsz i (Nat.le_trans (Nat.le_add_right i 1) h)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ei1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs `ys] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`hsz] [":" («term_=_» `xs.size "=" `ys.size)] [] ")")] [(Term.typeSpec ":" (Term.forall "∀" [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_≤_» `i "≤" `xs.size)] [] ")")] [] "," `Bool))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(num "0") "," (Term.hole "_")]] "=>" `true) (Term.matchAlt "|" [[(«term_+_» `i "+" (num "1")) "," `h]] "=>" («term_&&_» («term_==_» («term__[_]» `xs "[" `i "]") "==" («term__[_]'_» `ys "[" `i "]'" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.subst `hsz "▸" [`h]) ")"))) "&&" (Term.app `ei1 [`xs `ys `hsz `i (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Nat.le_trans [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Nat.le_add_right [`i (num "1")]) ")") `h]) ")")])))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def ei2 (xs : Array Nat) : Nat := match xs.size with\n  | 0 => #[1, 2].size\n  | n + 1 => n",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ei2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `xs.size)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.proj («term#[_,]» "#[" [(num "1") "," (num "2")] "]") "." `size)) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" `n)])) (Termination.suffix [] []) []) []))"##,
    },
];

/// `scoped instance` and `local instance`, also after a modifier: the instance's `attrKind`
/// (`Term.scoped`, `Term.local`).
const SCOPED_INSTANCES: &[Accepted] = &[
    Accepted {
        source: "scoped instance si1 : Inhabited Nat := ⟨0⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind [(Term.scoped "scoped")]) "instance" [] [(Command.declId `si1 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0")] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "local instance si2 : Inhabited Nat := ⟨1⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind [(Term.local "local")]) "instance" [] [(Command.declId `si2 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "1")] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "noncomputable scoped instance si3 : Inhabited Nat := ⟨2⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [(Command.noncomputable "noncomputable")] [] []) (Command.instance (Term.attrKind [(Term.scoped "scoped")]) "instance" [] [(Command.declId `si3 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "2")] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// Vector literals `#v[a, b]` and `#v[]` (`Vector.«term#v[_,]»`), and a term `letI` named by the
/// hole (`Term.letId (Term.hole "_")`).
const VECTORS_AND_HOLE_LOCALS: &[Accepted] = &[
    Accepted {
        source: "def vv1 : Vector Nat 2 := #v[1, 2]",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `vv1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Vector [`Nat (num "2")]))]) (Command.declValSimple ":=" (Vector.«term#v[_,]» "#v[" [(num "1") "," (num "2")] "]") (Termination.suffix [] []) []) []))"##,
    },
    Accepted {
        source: "def vv2 : Vector Nat 0 := #v[]",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `vv2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Vector [`Nat (num "0")]))]) (Command.declValSimple ":=" (Vector.«term#v[_,]» "#v[" [] "]") (Termination.suffix [] []) []) []))"##,
    },
    Accepted {
        source: "def li1 : Nat := letI _ : Inhabited Nat := ⟨0⟩; default",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `li1 []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.letI "letI" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (Term.hole "_")) [] [(Term.typeSpec ":" (Term.app `Inhabited [`Nat]))] ":=" (Term.anonymousCtor "⟨" [(num "0")] "⟩"))) ";" `default) (Termination.suffix [] []) []) []))"#,
    },
];

/// The tactic `if`: `tacIfThenElse`, and `tacDepIfThenElse` with `h :`; a nested `if` keeps its
/// own `else`.
const TACTIC_CONDITIONALS: &[Accepted] = &[
    Accepted {
        source: "theorem ti1 (n : Nat) : n = n := by\n  if h : n = 0 then\n    rfl\n  else\n    rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ti1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])) "else" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ti2 (b : Bool) : b = b := by\n  if b then rfl else rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ti2 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacIfThenElse "if" `b "then" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])) "else" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ti3 (a b : Nat) : a = a := by\n  if a = 0 then\n    if b = 0 then rfl else rfl\n  else\n    rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ti3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacIfThenElse "if" («term_=_» `a "=" (num "0")) "then" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacIfThenElse "if" («term_=_» `b "=" (num "0")) "then" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])) "else" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])) "else" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Scope commands (`namespace`, `section`, `end`, the five `open` forms, `universe`, `variable`,
/// `include`, `omit`, `set_option`), a module doc (`Command.moduleDoc`, split as a doc comment is)
/// and `Command.in` after `open` or `set_option`, through
/// `command_scope::trees::command_tree`. (`section`'s ident and `end`'s are `ident` and
/// `identWithPartialTrailingDot`, hence `end`'s extra null node.)
const SCOPE_COMMANDS: &[Accepted] = &[
    Accepted {
        source: "namespace A.B",
        tree: r#"(Command.namespace "namespace" `A.B)"#,
    },
    Accepted {
        source: "end A.B",
        tree: r#"(Command.end "end" [`A.B []])"#,
    },
    Accepted {
        source: "section",
        tree: r#"(Command.section (Command.sectionHeader [] [] [] []) "section" [])"#,
    },
    Accepted {
        source: "end",
        tree: r#"(Command.end "end" [])"#,
    },
    Accepted {
        source: "section S",
        tree: r#"(Command.section (Command.sectionHeader [] [] [] []) "section" [`S])"#,
    },
    Accepted {
        source: "end S",
        tree: r#"(Command.end "end" [`S []])"#,
    },
    Accepted {
        source: "open Nat List",
        tree: r#"(Command.open "open" (Command.openSimple [`Nat `List]))"#,
    },
    Accepted {
        source: "open Nat in\n  def x1 : Nat := 1",
        tree: r#"(Command.in (Command.open "open" (Command.openSimple [`Nat])) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `x1 []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) [])))"#,
    },
    Accepted {
        source: "open Nat (succ zero)",
        tree: r#"(Command.open "open" (Command.openOnly `Nat "(" [`succ `zero] ")"))"#,
    },
    Accepted {
        source: "open Nat hiding add",
        tree: r#"(Command.open "open" (Command.openHiding `Nat "hiding" [`add]))"#,
    },
    Accepted {
        source: "open Nat renaming add → plus, mul → times",
        tree: r#"(Command.open "open" (Command.openRenaming `Nat "renaming" [(Command.openRenamingItem `add "→" `plus) "," (Command.openRenamingItem `mul "→" `times)]))"#,
    },
    Accepted {
        source: "open scoped Nat",
        tree: r#"(Command.open "open" (Command.openScoped "scoped" [`Nat]))"#,
    },
    Accepted {
        source: "universe u v",
        tree: r#"(Command.universe "universe" [`u `v])"#,
    },
    Accepted {
        source: "variable (n : Nat) {m : Nat}",
        tree: r#"(Command.variable "variable" [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.implicitBinder "{" [`m] [":" `Nat] "}")])"#,
    },
    Accepted {
        source: "include n",
        tree: r#"(Command.include "include" [`n])"#,
    },
    Accepted {
        source: "omit n",
        tree: r#"(Command.omit "omit" [`n])"#,
    },
    Accepted {
        source: "set_option pp.all true",
        tree: r#"(Command.set_option "set_option" `pp.all [] "true")"#,
    },
    Accepted {
        source: "set_option maxRecDepth 2000 in\n  def x2 : Nat := 1",
        tree: r#"(Command.in (Command.set_option "set_option" `maxRecDepth [] (num "2000")) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `x2 []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) [])))"#,
    },
    Accepted {
        source: "set_option pp.all true in open Nat in\n  def x3 : Nat := 1",
        tree: r#"(Command.in (Command.set_option "set_option" `pp.all [] "true") "in" (Command.in (Command.open "open" (Command.openSimple [`Nat])) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `x3 []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (num "1") (Termination.suffix [] []) []) []))))"#,
    },
    Accepted {
        source: "noncomputable section",
        tree: r#"(Command.section (Command.sectionHeader [] [] ["noncomputable"] []) "section" [])"#,
    },
    Accepted {
        source: "end",
        tree: r#"(Command.end "end" [])"#,
    },
    Accepted {
        source: "/-! Module doc. -/",
        tree: r#"(Command.moduleDoc "/-!" "Module doc. -/")"#,
    },
];

/// `attribute [instances] names` (`Command.attribute`): the declaration attribute grammar between
/// `[` and `]`, and `eraseAttr` (`-simp`).
const ATTRIBUTE_COMMANDS: &[Accepted] = &[
    Accepted {
        source: "attribute [simp] t1",
        tree: r#"(Command.attribute "attribute" "[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] [] []))] "]" [`t1])"#,
    },
    Accepted {
        source: "attribute [-simp] t1",
        tree: r#"(Command.attribute "attribute" "[" [(Command.eraseAttr "-" `simp)] "]" [`t1])"#,
    },
    Accepted {
        source: "attribute [local simp] t1",
        tree: r#"(Command.attribute "attribute" "[" [(Term.attrInstance (Term.attrKind [(Term.local "local")]) (Attr.simp "simp" [] [] []))] "]" [`t1])"#,
    },
    Accepted {
        source: "attribute [simp, inline] t1",
        tree: r#"(Command.attribute "attribute" "[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] [] [])) "," (Term.attrInstance (Term.attrKind []) (Attr.simple `inline []))] "]" [`t1])"#,
    },
    Accepted {
        source: "attribute [local instance] t1",
        tree: r#"(Command.attribute "attribute" "[" [(Term.attrInstance (Term.attrKind [(Term.local "local")]) (Attr.instance "instance" []))] "]" [`t1])"#,
    },
    Accepted {
        source: "attribute [instance 100] t1",
        tree: r#"(Command.attribute "attribute" "[" [(Term.attrInstance (Term.attrKind []) (Attr.instance "instance" [(num "100")]))] "]" [`t1])"#,
    },
    Accepted {
        source: "attribute [reducible] t1",
        tree: r#"(Command.attribute "attribute" "[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))] "]" [`t1])"#,
    },
];

/// A `section` with a header, read by `parse_source_command` as a command the checker refuses.
const HEADED_SECTIONS: &[Accepted] = &[
    Accepted {
        source: "public section",
        tree: r#"(Command.section (Command.sectionHeader [] ["public"] [] []) "section" [])"#,
    },
    Accepted {
        source: "@[expose] public section",
        tree: r#"(Command.section (Command.sectionHeader ["@[" "expose" "]"] ["public"] [] []) "section" [])"#,
    },
    Accepted {
        source: "public section Foo",
        tree: r#"(Command.section (Command.sectionHeader [] ["public"] [] []) "section" [`Foo])"#,
    },
    Accepted {
        source: "public noncomputable section",
        tree: r#"(Command.section (Command.sectionHeader [] ["public"] ["noncomputable"] []) "section" [])"#,
    },
];

/// Simp rules marked to run before descent (`↓`, `Tactic.simpPre`), `Bool`'s `^^` (`Bool.«term_^^_»`), and
/// `ac_rfl`, `ext1` and `repeat'`.
const SIMP_ORDER_XOR_AND_TACTICS: &[Accepted] = &[
    Accepted {
        source: "theorem q1 (b : Bool) : (if b then 1 else 1) = 1 := by\n  simp only [↓reduceIte]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q1 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (termIfThenElse "if" `b "then" (num "1") "else" (num "1")) ")") "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q2 (a b : Bool) : (a ^^ b) = (b ^^ a) := by\n  cases a <;> cases b <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Bool.«term_^^_» `a "^^" `b) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Bool.«term_^^_» `b "^^" `a) ")")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `a)] [] []) "<;>" (Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] [])) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q3 (a b : Nat) : a + b = b + a := by\n  ac_rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `b "+" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.acRfl "ac_rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q4 (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by\n  ext1 x\n  exact h x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q4 []) (Command.declSig [(Term.explicitBinder "(" [`f `g] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`x] [] "," («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x])))] [] ")")] (Term.typeSpec ":" («term_=_» `f "=" `g))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.Elab.Tactic.Ext.tacticExt1___ "ext1" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))]) [] (Tactic.exact "exact" (Term.app `h [`x]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q5 (n : Nat) : n = n := by\n  repeat' rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q5 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.repeat' "repeat'" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem q6 (b : Bool) : (if b then 1 else 1) = 1 := by\n  simp [↓reduceIte, Nat.add_comm]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `q6 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (termIfThenElse "if" `b "then" (num "1") "else" (num "1")) ")") "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte) "," (Tactic.simpLemma [] [] `Nat.add_comm)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Syntax declarations (`Command.syntax`, `Command.syntaxAbbrev`) and the `stx` grammar: atoms,
/// `&"x"`, `unicode(…)`, categories with precedences, parentheses, functions of one and two
/// sequences, `sepBy(…)`, `!`, the postfixes and `<|>`; precedences and priorities in words and
/// sums. Through `parse_source_command`, which the checker's refusal follows.
const SYNTAX_DECLARATIONS: &[Accepted] = &[
    Accepted {
        source: "syntax \"funext\" (ppSpace colGt term:max)* : tactic",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"funext\"")) («stx_*» (Syntax.paren "(" [(Syntax.cat `ppSpace []) (Syntax.cat `colGt []) (Syntax.cat `term [(precedence ":" (precMax "max"))])] ")") "*")] ":" `tactic)"#,
    },
    Accepted {
        source: "syntax \"{\" term,+ \"}\" : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"{\"")) («stx_,+» (Syntax.cat `term []) ",+") (Syntax.atom (str "\"}\""))] ":" `term)"#,
    },
    Accepted {
        source: "syntax (name := rawNatLit) \"nat_lit \" num : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [(Command.namedName "(" "name" ":=" `rawNatLit ")")] [] [(Syntax.atom (str "\"nat_lit \"")) (Syntax.cat `num [])] ":" `term)"#,
    },
    Accepted {
        source: "syntax binderIdent := ident <|> hole",
        tree: r#"(Command.syntaxAbbrev [] [] "syntax" `binderIdent ":=" [(«stx_<|>_» (Syntax.cat `ident []) "<|>" (Syntax.cat `hole []))])"#,
    },
    Accepted {
        source: "syntax caseArg := binderIdent (ppSpace binderIdent)*",
        tree: r#"(Command.syntaxAbbrev [] [] "syntax" `caseArg ":=" [(Syntax.cat `binderIdent []) («stx_*» (Syntax.paren "(" [(Syntax.cat `ppSpace []) (Syntax.cat `binderIdent [])] ")") "*")])"#,
    },
    Accepted {
        source: "syntax \"iterate\" (ppSpace num)? ppSpace tacticSeq : tactic",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"iterate\"")) (stx_? (Syntax.paren "(" [(Syntax.cat `ppSpace []) (Syntax.cat `num [])] ")") "?") (Syntax.cat `ppSpace []) (Syntax.cat `tacticSeq [])] ":" `tactic)"#,
    },
    Accepted {
        source: "syntax cdotTk := unicode(\"· \", \". \")",
        tree: r#"(Command.syntaxAbbrev [] [] "syntax" `cdotTk ":=" [(Syntax.unicodeAtom "unicode(" (str "\"· \"") "," (str "\". \"") [] ")")])"#,
    },
    Accepted {
        source: "syntax simpAllKind := atomic(\" (\" &\"all\") \" := \" &\"true\" \")\"",
        tree: r#"(Command.syntaxAbbrev [] [] "syntax" `simpAllKind ":=" [(Syntax.unary `atomic "(" [(Syntax.atom (str "\" (\"")) (Syntax.nonReserved "&" (str "\"all\""))] ")") (Syntax.atom (str "\" := \"")) (Syntax.nonReserved "&" (str "\"true\"")) (Syntax.atom (str "\")\""))])"#,
    },
    Accepted {
        source: "syntax:65 (name := addPrec) prec \" + \" prec:66 : prec",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [(precedence ":" (num "65"))] [(Command.namedName "(" "name" ":=" `addPrec ")")] [] [(Syntax.cat `prec []) (Syntax.atom (str "\" + \"")) (Syntax.cat `prec [(precedence ":" (num "66"))])] ":" `prec)"#,
    },
    Accepted {
        source: "syntax (name := solveTactic) \"solve\" withPosition((ppDedent(ppLine) colGe \"| \" tacticSeq)+) : tactic",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [(Command.namedName "(" "name" ":=" `solveTactic ")")] [] [(Syntax.atom (str "\"solve\"")) (Syntax.unary `withPosition "(" [(«stx_+» (Syntax.paren "(" [(Syntax.unary `ppDedent "(" [(Syntax.cat `ppLine [])] ")") (Syntax.cat `colGe []) (Syntax.atom (str "\"| \"")) (Syntax.cat `tacticSeq [])] ")") "+")] ")")] ":" `tactic)"#,
    },
    Accepted {
        source: "scoped syntax \"wf_trivial\" : tactic",
        tree: r#"(Command.syntax [] [] (Term.attrKind [(Term.scoped "scoped")]) "syntax" [] [] [] [(Syntax.atom (str "\"wf_trivial\""))] ":" `tactic)"#,
    },
    Accepted {
        source: "syntax \"∃ \" binderIdent binderPred \", \" term : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"∃ \"")) (Syntax.cat `binderIdent []) (Syntax.cat `binderPred []) (Syntax.atom (str "\", \"")) (Syntax.cat `term [])] ":" `term)"#,
    },
    Accepted {
        source: "syntax (name := simpArith) \"simp_arith \" optConfig (discharger)? (&\" only\")? (\" [\" (simpStar <|> simpErase <|> simpLemma),* \"]\")? (location)? : tactic",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [(Command.namedName "(" "name" ":=" `simpArith ")")] [] [(Syntax.atom (str "\"simp_arith \"")) (Syntax.cat `optConfig []) (stx_? (Syntax.paren "(" [(Syntax.cat `discharger [])] ")") "?") (stx_? (Syntax.paren "(" [(Syntax.nonReserved "&" (str "\" only\""))] ")") "?") (stx_? (Syntax.paren "(" [(Syntax.atom (str "\" [\"")) («stx_,*» (Syntax.paren "(" [(«stx_<|>_» (Syntax.cat `simpStar []) "<|>" («stx_<|>_» (Syntax.cat `simpErase []) "<|>" (Syntax.cat `simpLemma [])))] ")") ",*") (Syntax.atom (str "\"]\""))] ")") "?") (stx_? (Syntax.paren "(" [(Syntax.cat `location [])] ")") "?")] ":" `tactic)"#,
    },
    Accepted {
        source: "syntax (priority := high) \"[\" withoutPosition(term,*,?) \"]\" : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [(Command.namedPrio "(" "priority" ":=" (prioHigh "high") ")")] [(Syntax.atom (str "\"[\"")) (Syntax.unary `withoutPosition "(" [(«stx_,*,?» (Syntax.cat `term []) ",*,?")] ")") (Syntax.atom (str "\"]\""))] ":" `term)"#,
    },
    Accepted {
        source: "syntax \"foo1\" !\"bar\" term : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"foo1\"")) (stx!_ "!" (Syntax.atom (str "\"bar\""))) (Syntax.cat `term [])] ":" `term)"#,
    },
    Accepted {
        source: "syntax \"foo2\" sepBy(term, \";\") : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"foo2\"")) (Syntax.sepBy "sepBy(" [(Syntax.cat `term [])] "," (str "\";\"") [] [] ")")] ":" `term)"#,
    },
    Accepted {
        source: "syntax \"foo3\" sepBy1(term, \";\", \"; \", allowTrailingSep) : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"foo3\"")) (Syntax.sepBy1 "sepBy1(" [(Syntax.cat `term [])] "," (str "\";\"") ["," [(Syntax.atom (str "\"; \""))]] ["," "allowTrailingSep"] ")")] ":" `term)"#,
    },
    Accepted {
        source: "syntax \"foo4\" orelse(term, num) : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"foo4\"")) (Syntax.binary `orelse "(" [(Syntax.cat `term [])] "," [(Syntax.cat `num [])] ")")] ":" `term)"#,
    },
    Accepted {
        source: "syntax:arg \"foo5\" term:lead : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [(precedence ":" (precArg "arg"))] [] [] [(Syntax.atom (str "\"foo5\"")) (Syntax.cat `term [(precedence ":" (precLead "lead"))])] ":" `term)"#,
    },
    Accepted {
        source: "syntax:min \"foo6\" term:arg : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [(precedence ":" (precMin "min"))] [] [] [(Syntax.atom (str "\"foo6\"")) (Syntax.cat `term [(precedence ":" (precArg "arg"))])] ":" `term)"#,
    },
    Accepted {
        source: "syntax:max \"foo7\" term:min1 : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [(precedence ":" (precMax "max"))] [] [] [(Syntax.atom (str "\"foo7\"")) (Syntax.cat `term [(precedence ":" (precMin1 "min1"))])] ":" `term)"#,
    },
    Accepted {
        source: "syntax (name := foo8) (priority := low) \"foo8\" : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [(Command.namedName "(" "name" ":=" `foo8 ")")] [(Command.namedPrio "(" "priority" ":=" (prioLow "low") ")")] [(Syntax.atom (str "\"foo8\""))] ":" `term)"#,
    },
    Accepted {
        source: "syntax (priority := default + 1) \"foo9\" : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [(Command.namedPrio "(" "priority" ":=" (Syntax.addPrio (prioDefault "default") "+" (num "1")) ")")] [(Syntax.atom (str "\"foo9\""))] ":" `term)"#,
    },
    Accepted {
        source: "/-- A doc. -/ syntax fooAbbrev := \"x\" <|> \"y\"",
        tree: r#"(Command.syntaxAbbrev [(Command.docComment "/--" "A doc. -/")] [] "syntax" `fooAbbrev ":=" [(«stx_<|>_» (Syntax.atom (str "\"x\"")) "<|>" (Syntax.atom (str "\"y\"")))])"#,
    },
    Accepted {
        source: "@[inherit_doc] syntax \"foo10\" : term",
        tree: r#"(Command.syntax [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `inherit_doc []))] "]")] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"foo10\""))] ":" `term)"#,
    },
    Accepted {
        source: "private syntax fooPriv := \"z\"",
        tree: r#"(Command.syntaxAbbrev [] [(Command.private "private")] "syntax" `fooPriv ":=" [(Syntax.atom (str "\"z\""))])"#,
    },
    Accepted {
        source: "syntax \"foo11\" term:(max+1) : term",
        tree: r#"(Command.syntax [] [] (Term.attrKind []) "syntax" [] [] [] [(Syntax.atom (str "\"foo11\"")) (Syntax.cat `term [(precedence ":" («prec(_)» "(" (Syntax.addPrec (precMax "max") "+" (num "1")) ")"))])] ":" `term)"#,
    },
];

/// Notations (`Command.mixfix` for `infix`, `infixl`, `infixr`, `prefix` and `postfix`;
/// `Command.notation` with its `identPrec` items) and `recommended_spelling`, through
/// `parse_source_command`, which the checker's refusal follows.
const NOTATION_DECLARATIONS: &[Accepted] = &[
    Accepted {
        source: "@[inherit_doc mapRev2] infixr:100 \" <&&> \" => mapRev2",
        tree: r#"(Command.mixfix [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `inherit_doc [`mapRev2]))] "]")] (Term.attrKind []) (Command.infixr "infixr") (precedence ":" (num "100")) [] [] (str "\" <&&> \"") "=>" `mapRev2)"#,
    },
    Accepted {
        source: "infix:50 \" ≈≈ \" => mapRev2",
        tree: r#"(Command.mixfix [] [] (Term.attrKind []) (Command.infix "infix") (precedence ":" (num "50")) [] [] (str "\" ≈≈ \"") "=>" `mapRev2)"#,
    },
    Accepted {
        source: "infixl:65 (name := plusPlus) \" +++ \" => mapRev2",
        tree: r#"(Command.mixfix [] [] (Term.attrKind []) (Command.infixl "infixl") (precedence ":" (num "65")) [(Command.namedName "(" "name" ":=" `plusPlus ")")] [] (str "\" +++ \"") "=>" `mapRev2)"#,
    },
    Accepted {
        source: "prefix:max \"√√\" => Nat.succ",
        tree: r#"(Command.mixfix [] [] (Term.attrKind []) (Command.prefix "prefix") (precedence ":" (precMax "max")) [] [] (str "\"√√\"") "=>" `Nat.succ)"#,
    },
    Accepted {
        source: "postfix:max \"⁺⁺\" => Nat.succ",
        tree: r#"(Command.mixfix [] [] (Term.attrKind []) (Command.postfix "postfix") (precedence ":" (precMax "max")) [] [] (str "\"⁺⁺\"") "=>" `Nat.succ)"#,
    },
    Accepted {
        source: "scoped notation:50 a \" ≺≺ \" b => mapRev2 a b",
        tree: r#"(Command.notation [] [] (Term.attrKind [(Term.scoped "scoped")]) "notation" [(precedence ":" (num "50"))] [] [] [(Command.identPrec `a []) (str "\" ≺≺ \"") (Command.identPrec `b [])] "=>" (Term.app `mapRev2 [`a `b]))"#,
    },
    Accepted {
        source: "notation \"‖\" x \"‖\" => Nat.succ x",
        tree: r#"(Command.notation [] [] (Term.attrKind []) "notation" [] [] [] [(str "\"‖\"") (Command.identPrec `x []) (str "\"‖\"")] "=>" (Term.app `Nat.succ [`x]))"#,
    },
    Accepted {
        source: "notation:max (priority := high) x:max \" !! \" y:65 => mapRev2 x y",
        tree: r#"(Command.notation [] [] (Term.attrKind []) "notation" [(precedence ":" (precMax "max"))] [] [(Command.namedPrio "(" "priority" ":=" (prioHigh "high") ")")] [(Command.identPrec `x [(precedence ":" (precMax "max"))]) (str "\" !! \"") (Command.identPrec `y [(precedence ":" (num "65"))])] "=>" (Term.app `mapRev2 [`x `y]))"#,
    },
    Accepted {
        source: "local notation \"ℕℕ\" => Nat",
        tree: r#"(Command.notation [] [] (Term.attrKind [(Term.local "local")]) "notation" [] [] [] [(str "\"ℕℕ\"")] "=>" `Nat)"#,
    },
    Accepted {
        source: "recommended_spelling \"mapRev\" for \"<&&>\" in [mapRev2, «term_<&&>_»]",
        tree: r#"(Command.recommended_spelling [] "recommended_spelling" (str "\"mapRev\"") "for" (str "\"<&&>\"") "in" "[" [`mapRev2 "," `«term_<&&>_»] "]")"#,
    },
    Accepted {
        source: "recommended_spelling \"plus\" for \"+++\" in [mapRev2]",
        tree: r#"(Command.recommended_spelling [] "recommended_spelling" (str "\"plus\"") "for" (str "\"+++\"") "in" "[" [`mapRev2] "]")"#,
    },
];

/// `generalize`: `generalizeArg,+` (a named equation `h :` optional) and a location.
const GENERALIZE_ARGUMENTS: &[Accepted] = &[
    Accepted {
        source: "theorem g1 (n : Nat) : n + 0 = n := by\n  generalize n + 0 = m\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.generalize "generalize" [(Tactic.generalizeArg [] («term_+_» `n "+" (num "0")) "=" `m)] []) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g2 (n : Nat) : n + 0 = n := by\n  generalize h : n + 0 = m\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.generalize "generalize" [(Tactic.generalizeArg [`h ":"] («term_+_» `n "+" (num "0")) "=" `m)] []) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g3 (n : Nat) (h0 : n = n) : n + 0 = n := by\n  generalize n + 0 = m at h0 ⊢\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h0] [":" («term_=_» `n "=" `n)] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.generalize "generalize" [(Tactic.generalizeArg [] («term_+_» `n "+" (num "0")) "=" `m)] [(Tactic.location "at" (Tactic.locationHyp [`h0 (Tactic.locationType (patternIgnore (token.«⊢» "⊢")))]))]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `first`'s alternatives, each a `group` of its `|` and its sequence, and `try` (`tacticTry_`), in
/// `<;>` chains.
const FIRST_AND_TRY: &[Accepted] = &[
    Accepted {
        source: "theorem c1 (a b : Bool) : a = a := by\n  cases a <;> cases b <;> first | rfl | rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `a)] [] []) "<;>" (Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] [])) "<;>" (Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c2 (n : Nat) : n = n := by\n  cases n <;> (try rfl) <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] []) "<;>" (Tactic.paren "(" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])) ")")) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A documented constructor (its `ctor`'s optional doc slot holds the `docComment`) and `repeat`
/// (`tacticRepeat_`).
const CONSTRUCTOR_DOCS_AND_REPEAT: &[Accepted] = &[
    Accepted {
        source: "inductive T1 where\n  /-- A doc. -/\n  | a : T1\n  | b : T1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `T1 []) (Command.optDeclSig [] []) ["where"] [(Command.ctor [(Command.docComment "/--" "A doc. -/")] "|" (Command.declModifiers [] [] [] [] [] [] []) `a (Command.optDeclSig [] [(Term.typeSpec ":" `T1)])) (Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `b (Command.optDeclSig [] [(Term.typeSpec ":" `T1)]))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "theorem r1 (n : Nat) : n = n := by\n  repeat rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRepeat_ "repeat" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Line-separated fields closed by a `}` left of them: `checkColEq` fails there, so no trailing
/// separator.
const FIELDS_CLOSED_LEFT_OF_THEM: &[Accepted] = &[
    Accepted {
        source: "def c7 : P3 := {\n    x := 1\n    y := 2\n  }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c7 []) (Command.optDeclSig [] [(Term.typeSpec ":" `P3)]) (Command.declValSimple ":=" (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (num "1"))]) [] (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "2"))])]) (Term.optEllipsis []) [] "}") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def c8 : P3 := { x := 1\n                 y := 2\n }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `c8 []) (Command.optDeclSig [] [(Term.typeSpec ":" `P3)]) (Command.declValSimple ":=" (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `x []) [[] [] (Term.structInstFieldDef ":=" [] (num "1"))]) [] (Term.structInstField (Term.structInstLVal `y []) [[] [] (Term.structInstFieldDef ":=" [] (num "2"))])]) (Term.optEllipsis []) [] "}") (Termination.suffix [] []) []) []))"#,
    },
];

/// Operators of equal precedence and different associativity: the previous operator's right operand
/// decides (`|>`'s is `term:min1`, `<|`'s `term:min`).
const MIXED_ASSOCIATIVITY: &[Accepted] = &[
    Accepted {
        source: "def mp1 (a b : Nat) : Nat := a |> Nat.sub <| b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mp1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_<|_» («term_|>_» `a "|>" `Nat.sub) "<|" `b) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def mp2 (a b c : Nat) : Nat := a <| b |> c",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mp2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_<|_» `a "<|" («term_|>_» `b "|>" `c)) (Termination.suffix [] []) []) []))"#,
    },
];

/// `let rec`'s keywords (a `group` node) and `solve_by_elim` (`Tactic.solveByElim` with its optional
/// slots).
const LET_REC_AND_SOLVE_BY_ELIM: &[Accepted] = &[
    Accepted {
        source: "def lr1 : Nat := let rec go (n : Nat) : Nat := n; go 3",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lr1 []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `n)) (Termination.suffix [] []))]) ";" (Term.app `go [(num "3")])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem sbe (p : Prop) (h : p) : p := by\n  solve_by_elim",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sbe []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.solveByElim "solve_by_elim" [] (Tactic.optConfig []) [] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `conv` blocks (`at h`, `in e`) and the conv tactics `lhs`, `rhs`, `congr`, `arg n`, `enter [n, …]`,
/// `ext x` and `rw [rules]`, separated by `;` or by lines.
const CONV_BLOCKS: &[Accepted] = &[
    Accepted {
        source: "theorem cv1 (a b : Nat) (h : a = b) : a + 0 = b := by\n  conv => lhs; rw [Nat.add_zero]\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cv1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))]))) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cv2 (a b : Nat) (h : a = b) : a = b + 0 := by\n  conv =>\n    rhs\n    rw [Nat.add_zero]\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cv2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" («term_+_» `b "+" (num "0"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.rhs "rhs") [] (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))]))) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cv3 (a b : Nat) (h : a + 0 = b) : a = b := by\n  conv at h => lhs; rw [Nat.add_zero]\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cv3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» («term_+_» `a "+" (num "0")) "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" ["at" `h] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))]))) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cv4 (f : Nat → Nat) (a : Nat) : f (a + 0) = f a := by\n  conv => lhs; arg 1; rw [Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cv4 []) (Command.declSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `a "+" (num "0")) ")")]) "=" (Term.app `f [`a])))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.arg "arg" (Tactic.Conv.argArg [] [] (num "1"))) ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cv5 (f : Nat → Nat → Nat) (a b : Nat) : f a (b + 0) = f a b := by\n  conv => enter [1, 2]; rw [Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cv5 []) (Command.declSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" (Term.arrow `Nat "→" `Nat))] [] ")") (Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [`a (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `b "+" (num "0")) ")")]) "=" (Term.app `f [`a `b])))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.enter "enter" "[" [(Tactic.Conv.enterArg (Tactic.Conv.argArg [] [] (num "1"))) "," (Tactic.Conv.enterArg (Tactic.Conv.argArg [] [] (num "2")))] "]") ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cv6 (a : Nat) : (fun x => x + 0) a = a := by\n  conv => lhs; congr; ext x; rw [Nat.add_zero]\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cv6 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_+_» `x "+" (num "0")))) ")") [`a]) "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.congr "congr") ";" (Tactic.Conv.ext "ext" [(Lean.binderIdent `x)]) ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))]))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cv7 (a : Nat) : a + 0 = a := by\n  conv in a + 0 => rw [Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cv7 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] ["in" [] («term_+_» `a "+" (num "0"))] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `infer_instance`, `exfalso`, `clear` with names and `norm_cast` with a location.
const LEAF_TACTICS_TWO: &[Accepted] = &[
    Accepted {
        source: "theorem l1 : Inhabited Nat := by\n  infer_instance",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l1 []) (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l2 (h : False) : 1 = 2 := by\n  exfalso\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l2 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" `False] [] ")")] (Term.typeSpec ":" («term_=_» (num "1") "=" (num "2")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticExfalso "exfalso") [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l3 (a : Nat) (h : a = a) : True := by\n  clear h\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l3 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `a)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.clear "clear" [`h]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l4 (a b : Nat) (h : (a : Int) = b) : a = b := by\n  norm_cast at h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l4 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `a ":" [`Int] ")") "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticNorm_cast__ "norm_cast" (Tactic.optConfig []) [(Tactic.location "at" (Tactic.locationHyp [`h]))])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l5 (a : Nat) (h1 h2 : a = a) : True := by\n  clear h1 h2\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l5 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1 `h2] [":" («term_=_» `a "=" `a)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.clear "clear" [`h1 `h2]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Conv mode's `·` (a nested sequence), `apply e` and `simp`.
const CONV_FOCUS_APPLY_SIMP: &[Accepted] = &[
    Accepted {
        source: "theorem cw1 (a b : Nat) (h : a = b) : a + 0 = b + 0 := by\n  conv =>\n    congr\n    · rw [Nat.add_zero]\n    · rw [Nat.add_zero]\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cw1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" («term_+_» `b "+" (num "0"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.congr "congr") [] (Tactic.Conv.«conv·_» "·" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))]))) [] (Tactic.Conv.«conv·_» "·" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))])))]))) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cw2 (a : Nat) : a = a := by\n  conv => rhs; apply id",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cw2 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.rhs "rhs") ";" (Tactic.Conv.convApply_ "apply" `id)])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cw3 (a : Nat) : a + 0 = a := by\n  conv => lhs; simp only [Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cw3 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] `Nat.add_zero)] "]"])])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Instance priorities in words and sums (`prioLow`, `Syntax.addPrio`); the elaborator reads a numeral
/// only.
const WORD_PRIORITIES: &[Accepted] = &[
    Accepted {
        source: "instance (priority := low) inst1 : Inhabited Nat := ⟨0⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [(Command.namedPrio "(" "priority" ":=" (prioLow "low") ")")] [(Command.declId `inst1 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0")] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "instance (priority := default + 1) inst2 : Inhabited Nat := ⟨1⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [(Command.namedPrio "(" "priority" ":=" (Syntax.addPrio (prioDefault "default") "+" (num "1")) ")")] [(Command.declId `inst2 [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "1")] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// An index proof keeps the projections touching it: `xs[i]'(h).1` projects the proof.
const INDEX_PROOF_PROJECTIONS: &[Accepted] = &[Accepted {
    source: "def ip (xs : Array Nat) (i : Nat) (h : i < xs.size ∧ True) : Nat := xs[i]'(h).1",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ip []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» («term_<_» `i "<" `xs.size) "∧" `True)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term__[_]'_» `xs "[" `i "]'" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `h ")") "." (fieldIdx "1"))) (Termination.suffix [] []) []) []))"#,
}];

/// A local function in `do`, `let f x := e`: `letIdDecl` with the names as binders.
const DO_LOCAL_FUNCTIONS: &[Accepted] = &[Accepted {
    source: "def dl (n : Nat) : Id Nat := do\n  let f x := x + n\n  return f 1",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dl []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" [] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `f) [`x] [] ":=" («term_+_» `x "+" `n)))) []) (Term.doSeqItem (Term.doReturn "return" [(Term.app `f [(num "1")])]) [])])) (Termination.suffix [] []) []) []))"#,
}];

/// A `by` inside a tactic's term takes the `;`s after it: `exact f <| by t; u` runs `u` in the nested
/// proof.
const NESTED_BY_SEQUENCES: &[Accepted] = &[Accepted {
    source: "theorem nb (p : Prop) (h : p) : p ∧ p := by\n  exact And.intro h <| by exact h; skip",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `nb []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `p] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `p))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" («term_<|_» (Term.app `And.intro [`h]) "<|" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h) ";" (Tactic.skip "skip")])))))]))) (Termination.suffix [] []) [])))"#,
}];

/// A tactic `if`'s `else` branch takes the `;`s after it.
const ELSE_BRANCH_SEQUENCES: &[Accepted] = &[Accepted {
    source: "theorem ie (n : Nat) : n = n := by\n  if h : n = 0 then rfl else rfl; skip",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ie []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])) "else" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl") ";" (Tactic.skip "skip")])))]))) (Termination.suffix [] []) [])))"#,
}];

/// Applicative sequencing (`<*>`, `<*`, `*>`, left-associative at 60) and `≍` (`HEq`, at 50).
const SEQUENCING_AND_HEQ: &[Accepted] = &[
    Accepted {
        source: "def ap1 (f : Option (Nat → Nat)) (x : Option Nat) : Option Nat := f <*> x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ap1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow `Nat "→" `Nat) ")")])] [] ")") (Term.explicitBinder "(" [`x] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_<*>_» `f "<*>" `x) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ap2 (x y : Option Nat) : Option Nat := x <* y",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ap2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x `y] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_<*_» `x "<*" `y) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ap3 (x y : Option Nat) : Option Nat := x *> y",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ap3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`x `y] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_*>_» `x "*>" `y) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem he (a : Nat) : a ≍ a := HEq.rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `he []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_≍_» `a "≍" `a))) (Command.declValSimple ":=" `HEq.rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def ap4 (f g : Option (Nat → Nat)) (x : Option Nat) : Option Nat := f <*> x <* g <*> x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ap4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f `g] [":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow `Nat "→" `Nat) ")")])] [] ")") (Term.explicitBinder "(" [`x] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_<*>_» («term_<*_» («term_<*>_» `f "<*>" `x) "<*" `g) "<*>" `x) (Termination.suffix [] []) []) []))"#,
    },
];

/// Named patterns, `x@p` (`Term.namedPattern`), in equations and match rows.
const NAMED_PATTERNS: &[Accepted] = &[
    Accepted {
        source: "def np1 : List Nat → Nat\n  | l@(x :: _) => x + l.length\n  | [] => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `np1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.app `List [`Nat]) "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.namedPattern `l "@" [] (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_::_» `x "::" (Term.hole "_")) ")"))]] "=>" («term_+_» `x "+" `l.length)) (Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" (num "0"))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def np2 (p : Nat × Nat) : Nat :=\n  match p with\n  | q@⟨a, _⟩ => a + q.2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `np2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `p)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.namedPattern `q "@" [] (Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩"))]] "=>" («term_+_» `a "+" (Term.proj `q "." (fieldIdx "2"))))])) (Termination.suffix [] []) []) []))"#,
    },
];

/// Ascribed patterns, `(p : T)` (`Term.typeAscription`), in equations.
const ASCRIBED_PATTERNS: &[Accepted] = &[
    Accepted {
        source: "def asc1 : Option Nat → Nat\n  | some (n : Nat) => n\n  | none => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `asc1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.app `Option [`Nat]) "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [(Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `n ":" [`Nat] ")")])]] "=>" `n) (Term.matchAlt "|" [[`none]] "=>" (num "0"))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def asc2 : Nat → Nat\n  | (_ + 1 : Nat) => 1\n  | 0 => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `asc2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.hole "_") "+" (num "1")) ":" [`Nat] ")")]] "=>" (num "1")) (Term.matchAlt "|" [[(num "0")]] "=>" (num "0"))]) (Termination.suffix [] []) [])) []))"#,
    },
];

/// A structure's named constructor (`structCtor`, `mk ::`) and a private field (the field's
/// `declModifiers`); the elaborator refuses both.
const STRUCTURE_CONSTRUCTORS_AND_PRIVATE_FIELDS: &[Accepted] = &[
    Accepted {
        source: "structure S1 where\n  mk ::\n  x : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `S1 []) (Command.optDeclSig [] []) [] ["where" [(Command.structCtor (Command.declModifiers [] [] [] [] [] [] []) `mk [] "::")] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "structure S3 where\n  private x : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `S3 []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
];

/// A protected field: `protected` has its own `declModifiers` slot.
const PROTECTED_FIELDS: &[Accepted] = &[Accepted {
    source: "structure S5 where\n  protected x : Nat",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `S5 []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [(Command.protected "protected")] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
}];

/// `nofun` (`Term.nofun`) and `nomatch e, …` (`Term.nomatch`).
const EMPTY_MATCHES: &[Accepted] = &[
    Accepted {
        source: "def nf1 : Empty → Nat := nofun",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `nf1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Empty "→" `Nat))]) (Command.declValSimple ":=" (Term.nofun "nofun") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def nm1 (h : False) : Nat := nomatch h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `nm1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`h] [":" `False] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.nomatch "nomatch" [`h]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def nm2 (h : False) (g : False) : Nat := nomatch h, g",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `nm2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`h] [":" `False] [] ")") (Term.explicitBinder "(" [`g] [":" `False] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.nomatch "nomatch" [`h "," `g]) (Termination.suffix [] []) []) []))"#,
    },
];

/// `deriving instance C, … for T, …` (`Command.deriving`).
const DERIVING_COMMANDS: &[Accepted] = &[
    Accepted {
        source: "deriving instance BEq for Option",
        tree: r#"(Command.deriving "deriving" [] "instance" [(Command.derivingClass [] `BEq)] "for" [`Option])"#,
    },
    Accepted {
        source: "deriving instance Inhabited for NonScalar, PNonScalar, True",
        tree: r#"(Command.deriving "deriving" [] "instance" [(Command.derivingClass [] `Inhabited)] "for" [`NonScalar "," `PNonScalar "," `True])"#,
    },
];

/// `t <;> u` across a line break on either side of its `<;>`.
const CHAINS_ACROSS_LINES: &[Accepted] = &[
    Accepted {
        source: "theorem sc (b : Bool) : b = b := by\n  cases b <;>\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sc []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem sc2 (b : Bool) : b = b := by\n  cases b\n  <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sc2 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `with tac` before the alternatives (`inductionAlts`' tactic slot) and a `_` alternative
/// (`Term.hole`).
const WITH_TACTICS_AND_WILDCARD_ALTERNATIVES: &[Accepted] = &[
    Accepted {
        source: "theorem iw1 (xs : List Nat) : xs = xs := by\n  induction xs with try rfl\n  | cons x xs ih => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `iw1 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» `xs "=" `xs))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `xs)] [] [] [(Tactic.inductionAlts "with" [(Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `cons) [`x `xs `ih])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem iw2 (n : Nat) : n = n := by\n  cases n with\n  | _ => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `iw2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (Term.hole "_") [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem iw3 (xs : List Nat) : xs = xs := by\n  cases xs with | _ => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `iw3 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» `xs "=" `xs))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `xs)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (Term.hole "_") [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `where` declarations with a doc comment and with attributes (`letRecDecl`'s first two slots).
const WHERE_DOCS_AND_ATTRIBUTES: &[Accepted] = &[
    Accepted {
        source: "def wd (n : Nat) : Nat := go n where\n  /-- The step. -/\n  go (k : Nat) : Nat := k + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wd []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `go [`n]) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [(Command.docComment "/--" "The step. -/")] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" («term_+_» `k "+" (num "1")))) (Termination.suffix [] []))] [])]) []))"#,
    },
    Accepted {
        source: "theorem wd_ok : wd 2 = 3 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `wd_ok []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.app `wd [(num "2")]) "=" (num "3")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def wa (n : Nat) : Nat := go n where\n  @[specialize] go (k : Nat) : Nat := k",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wa []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `go [`n]) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.specialize "specialize" []))] "]")] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `k)) (Termination.suffix [] []))] [])]) []))"#,
    },
];

/// `let rec @[attr] f …`: the attributes fill `letRecDecl`'s second slot.
const LET_REC_ATTRIBUTES: &[Accepted] = &[Accepted {
    source: "def lra (n : Nat) : Nat :=\n  let rec @[specialize] go (k : Nat) : Nat := k\n  go n",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lra []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.specialize "specialize" []))] "]")] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `k)) (Termination.suffix [] []))]) [] (Term.app `go [`n])) (Termination.suffix [] []) []) []))"#,
}];

/// `a <|> b` (`syntax:20 term:21 " <|> " term:20`, right-associative), `exists e, …`
/// (`"exists" term,+`), `generalize x = y, z = w` (whose commas stay in the `by` block), and `done`
/// (`syntax (name := done) "done" : tactic`), alone or inside a parenthesized sequence.
const ORELSE_EXISTS_AND_DONE: &[Accepted] = &[
    Accepted {
        source: "def oe (a b : Option Nat) : Option Nat := a <|> b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `oe []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_<|>_» `a "<|>" `b) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem ex1 : ∃ n : Nat, n = 1 := by\n  exists 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ex1 []) (Command.declSig [] (Term.typeSpec ":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" `Nat])) "," («term_=_» `n "=" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tacticExists_,,» "exists" [(num "1")])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem dn (n : Nat) : n = n := by\n  (rfl; done)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `dn []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.paren "(" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl") ";" (Tactic.done "done")])) ")")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def oe2 (a b c : Option Nat) : Option Nat := a <|> b <|> c",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `oe2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b `c] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_<|>_» `a "<|>" («term_<|>_» `b "<|>" `c)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem ex2 : ∃ a b : Nat, a + b = 3 := by exists 1, 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ex2 []) (Command.declSig [] (Term.typeSpec ":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a) (Lean.binderIdent `b)] [":" `Nat])) "," («term_=_» («term_+_» `a "+" `b) "=" (num "3"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tacticExists_,,» "exists" [(num "1") "," (num "2")])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem gm (x z : Nat) : x + z = z + x := by\n  generalize x = y, z = w\n  exact Nat.add_comm y w",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `gm []) (Command.declSig [(Term.explicitBinder "(" [`x `z] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `x "+" `z) "=" («term_+_» `z "+" `x)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.generalize "generalize" [(Tactic.generalizeArg [] `x "=" `y) "," (Tactic.generalizeArg [] `z "=" `w)] []) [] (Tactic.exact "exact" (Term.app `Nat.add_comm [`y `w]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem dn2 : True := by\n  trivial\n  done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `dn2 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial") [] (Tactic.done "done")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def oe3 (a b : Option Nat) (f : Nat → Option Nat) : Option Nat := a <|> b >>= f",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `oe3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" (Term.app `Option [`Nat])] [] ")") (Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" (Term.app `Option [`Nat]))] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" («term_<|>_» `a "<|>" («term_>>=_» `b ">>=" `f)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem fd (p : Prop) (hp : p) : p := by\n  first | (exact hp; done) | assumption",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `fd []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.paren "(" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp) ";" (Tactic.done "done")])) ")")]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.assumption "assumption")])))])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `t <;> u` whose `u` takes a `tacticSeq` (`try`, `first`, `all_goals`): `u` takes the `;`s and
/// `<;>`s after it, to the end of its line.
const CHAINED_SEQUENCES: &[Accepted] = &[
    Accepted {
        source: "theorem td (a b : Nat) : True := by\n  cases h₂ : a == b <;> try simp; done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `td []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [(Lean.binderIdent `h₂) ":"] («term_==_» `a "==" `b))] [] []) "<;>" (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []) ";" (Tactic.done "done")]))))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem td2 (p : Prop) (hp : p) : p := by\n  try exact hp; done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `td2 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp) ";" (Tactic.done "done")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem td3 (a b : Nat) : True := by\n  cases h₂ : a == b <;> try simp\n  done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `td3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [(Lean.binderIdent `h₂) ":"] («term_==_» `a "==" `b))] [] []) "<;>" (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])])))) [] (Tactic.done "done")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem td4 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor <;> first | exact hp | exact hq; done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `td4 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq) ";" (Tactic.done "done")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem td5 (a b : Nat) : True := by\n  cases h₂ : a == b <;> simp <;> try rfl; done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `td5 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [(Lean.binderIdent `h₂) ":"] («term_==_» `a "==" `b))] [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])) "<;>" (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl") ";" (Tactic.done "done")]))))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem td6 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor <;> all_goals first | exact hp | exact hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `td6 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq)])))])]))))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `cases a, b` and `induction a, b using r generalizing x with …`: `sepBy1(elimTarget, ", ")`,
/// each target with its own `h :`. The target list's commas stay in the `by` block; a comma after
/// the list (`⟨by cases b <;> rfl, trivial⟩`) still ends it.
const ELIMINATION_TARGETS: &[Accepted] = &[
    Accepted {
        source: "theorem mt1 (a b : Nat) : a + b = b + a := by\n  induction a, b using Nat.le_induction <;> simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `mt1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `b "+" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.induction "induction" [(Tactic.elimTarget [] `a) "," (Tactic.elimTarget [] `b)] ["using" `Nat.le_induction] [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem mt2 (a b : Bool) : (a && b) = (b && a) := by\n  cases a, b <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `mt2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_&&_» `a "&&" `b) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_&&_» `b "&&" `a) ")")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `a) "," (Tactic.elimTarget [] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem mt3 (a b : Bool) : (a && b) = (b && a) := by\n  cases h₁ : a, h₂ : b <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `mt3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_&&_» `a "&&" `b) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_&&_» `b "&&" `a) ")")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [(Lean.binderIdent `h₁) ":"] `a) "," (Tactic.elimTarget [(Lean.binderIdent `h₂) ":"] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem mt4 (m n : Nat) : m + n = n + m := by\n  induction m, n using Nat.strongRecOn generalizing m with\n  | ind n ih => omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `mt4 []) (Command.declSig [(Term.explicitBinder "(" [`m `n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `m "+" `n) "=" («term_+_» `n "+" `m)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `m) "," (Tactic.elimTarget [] `n)] ["using" `Nat.strongRecOn] ["generalizing" [`m]] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `ind) [`n `ih])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem bc1 (b : Bool) : b = b ∧ True := ⟨by cases b <;> rfl, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bc1 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» `b "=" `b) "∧" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem bc2 (b : Bool) : True ∧ b = b := ⟨trivial, by cases b <;> rfl⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bc2 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_∧_» `True "∧" («term_=_» `b "=" `b)))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [`trivial "," (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl"))])))] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem bc3 (b : Bool) : b = b ∧ True := ⟨by cases b with | true => rfl | false => rfl, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bc3 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» `b "=" `b) "∧" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `true) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `false) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem bc4 (n : Nat) : n = n ∧ True := ⟨by induction n <;> rfl, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bc4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» `n "=" `n) "∧" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.induction "induction" [(Tactic.elimTarget [] `n)] [] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem bc5 (x : Nat) : x = x ∧ True := ⟨by generalize x = y; rfl, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bc5 []) (Command.declSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» `x "=" `x) "∧" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.generalize "generalize" [(Tactic.generalizeArg [] `x "=" `y)] []) ";" (Tactic.tacticRfl "rfl")]))) "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// `(" using " term)?`: an eliminator that is any term (`Nat.rec (motive := …)`), up to
/// `generalizing` or `with`.
const USING_TERMS: &[Accepted] = &[
    Accepted {
        source: "theorem ut1 (t : Nat) (k : Nat) : t = t := by\n  induction t, k using Nat.rec (motive := fun _ => True) <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ut1 []) (Command.declSig [(Term.explicitBinder "(" [`t] [":" `Nat] [] ")") (Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `t "=" `t))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.induction "induction" [(Tactic.elimTarget [] `t) "," (Tactic.elimTarget [] `k)] ["using" (Term.app `Nat.rec [(Term.namedArgument "(" `motive ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `True)) ")")])] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ut2 (t : Nat) : t = t := by\n  induction t using Nat.strongRecOn generalizing k with\n  | ind n ih => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ut2 []) (Command.declSig [(Term.explicitBinder "(" [`t] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `t "=" `t))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `t)] ["using" `Nat.strongRecOn] ["generalizing" [`k]] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `ind) [`n `ih])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ut3 (t : Nat) : t = t := by\n  cases t using Nat.casesAuxOn",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ut3 []) (Command.declSig [(Term.explicitBinder "(" [`t] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `t "=" `t))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `t)] ["using" `Nat.casesAuxOn] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ut4 (t : Nat) : t = t := by\n  induction t using Nat.rec",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ut4 []) (Command.declSig [(Term.explicitBinder "(" [`t] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `t "=" `t))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `t)] ["using" `Nat.rec] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A `case`/`next` body on its own line: a `tacticSeq` positioned at its first token, which takes
/// every line at that column, the enclosing sequence's included (`case succ` inside `case zero`).
const CASE_BODIES: &[Accepted] = &[
    Accepted {
        source: "theorem cb1 (n : Nat) : n = n := by\n  induction n\n  · case zero =>\n    rfl\n  · case succ n ih =>\n    rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cb1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] [] [] []) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `zero) [])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `succ) [(Lean.binderIdent `n) (Lean.binderIdent `ih)])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cb2 (n : Nat) : n = n := by\n  cases n\n  case zero =>\n  rfl\n  case succ n =>\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cb2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] []) [] (Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `zero) [])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl") [] (Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `succ) [(Lean.binderIdent `n)])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cb3 (n : Nat) : n = n := by\n  cases n\n  next =>\n    rfl\n  next n =>\n    rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cb3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] []) [] (Tactic.«tacticNext_=>_» "next" [] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) [] (Tactic.«tacticNext_=>_» "next" [(Lean.binderIdent `n)] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cb4 (n : Nat) : n = n := by\n  cases n\n  · case zero => rfl\n  · case succ n =>\n    skip\n    rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cb4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] []) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `zero) [])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.case "case" [(Tactic.caseArg (Lean.binderIdent `succ) [(Lean.binderIdent `n)])] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip") [] (Tactic.tacticRfl "rfl")])))])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `conv => a <;> b`: the conv sequence's own `conv_<;>_` (`y:conv:0`, nested to the right), never
/// the tactic `<;>` around a whole `conv`; a `conv` after a tactic `<;>` takes the rest of the line.
const CONV_CHAINS: &[Accepted] = &[
    Accepted {
        source: "theorem cc (a b : Nat) : a + b = b + a := by\n  conv => congr <;> rw [Nat.add_comm]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cc []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `b "+" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.«conv_<;>_» (Tactic.Conv.congr "congr") "<;>" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_comm)] "]")))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cc2 (a b : Nat) : a + b = b + a := by\n  all_goals try\n    conv => congr <;> rw [Nat.add_comm]\n    simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cc2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `b "+" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.«conv_<;>_» (Tactic.Conv.congr "congr") "<;>" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_comm)] "]")))]))) [] (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])])))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cc3 (a b : Nat) : a + b = b + a := by\n  skip <;> conv => congr <;> rw [Nat.add_comm]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cc3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `b "+" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.skip "skip") "<;>" (Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.«conv_<;>_» (Tactic.Conv.congr "congr") "<;>" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_comm)] "]")))]))))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cc4 (a b : Nat) : a + b = b + a := by\n  conv => lhs <;> rw [Nat.add_comm] <;> skip",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cc4 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `b "+" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.«conv_<;>_» (Tactic.Conv.lhs "lhs") "<;>" (Tactic.Conv.«conv_<;>_» (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_comm)] "]")) "<;>" (Tactic.Conv.skip "skip")))])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `show t`, `erw`, `rw_mod_cast`, `rotate_left n`, `subst_eqs`, `injections h…`, and a
/// configuration's `valConfigItem` (`(occs := [1])`, `(config := { … })`) beside `+opt`.
const LEAF_TACTICS_THREE: &[Accepted] = &[
    Accepted {
        source: "theorem l1 (n : Nat) : n = n := by\n  show n = n\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.show "show" («term_=_» `n "=" `n)) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l2 (a b : Nat) (h : a = b) : b = a := by\n  erw [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticErw___ "erw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l3 (a b : Nat) (h : a = b) (h' : b = a) : b = a := by\n  erw [h] at h'\n  exact h'",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h'] [":" («term_=_» `b "=" `a)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticErw___ "erw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [(Tactic.location "at" (Tactic.locationHyp [`h']))]) [] (Tactic.exact "exact" `h')]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l4 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  rotate_left\n  exact hq\n  exact hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l4 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Tactic.rotateLeft "rotate_left" []) [] (Tactic.exact "exact" `hq) [] (Tactic.exact "exact" `hp)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l5 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  rotate_left 1\n  exact hq\n  exact hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l5 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Tactic.rotateLeft "rotate_left" [(num "1")]) [] (Tactic.exact "exact" `hq) [] (Tactic.exact "exact" `hp)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l6 (a b : Nat) (h : a = b) : b = a := by\n  subst_eqs\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l6 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.substEqs "subst_eqs") [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l7 (a b : Nat) (h : a + 1 = b + 1) : a = b := by\n  injections\n  omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l7 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» («term_+_» `a "+" (num "1")) "=" («term_+_» `b "+" (num "1")))] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.injections "injections" []) [] (Tactic.omega "omega" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l8 (a b : Nat) (h : a + 1 = b + 1) : a = b := by\n  injections h1 h2\n  omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l8 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» («term_+_» `a "+" (num "1")) "=" («term_+_» `b "+" (num "1")))] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.injections "injections" [`h1 `h2]) [] (Tactic.omega "omega" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l10 (a b : Nat) (h : a = b) : b = a := by\n  rw_mod_cast [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l10 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRw_mod_cast___ "rw_mod_cast" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ro1 (a b : Nat) (h : a = b) : b = a := by\n  rw (occs := [1]) [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ro1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig [(Tactic.configItem (Tactic.valConfigItem "(" `occs ":=" («term[_]» "[" [(num "1")] "]") ")"))]) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ro2 (a b : Nat) (h : a = b) : b = a := by\n  rw (occs := .pos [2]) [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ro2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig [(Tactic.configItem (Tactic.valConfigItem "(" `occs ":=" (Term.app (Term.dotIdent "." `pos) [(«term[_]» "[" [(num "2")] "]")]) ")"))]) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ro3 (n : Nat) : n + 0 = n := by\n  simp (config := { decide := true })",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ro3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig [(Tactic.configItem (Tactic.valConfigItem "(" `config ":=" (Term.structInst "{" [] (Term.structInstFields [(Term.structInstField (Term.structInstLVal `decide []) [[] [] (Term.structInstFieldDef ":=" [] `true)])]) (Term.optEllipsis []) [] "}") ")"))]) [] [] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ro4 (n : Nat) : n + 0 = n := by\n  simp +arith (maxSteps := 10)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ro4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig [(Tactic.configItem (Tactic.posConfigItem "+" `arith)) (Tactic.configItem (Tactic.valConfigItem "(" `maxSteps ":=" (num "10") ")"))]) [] [] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Bare binders in a declaration's or a local definition's header (`def bb1 α [Inhabited α]`,
/// `let f x := …`: `binderIdent <|> bracketedBinder`) and an application pattern's trailing ellipsis
/// (`.succ ..`, `Term.ellipsis`).
const BARE_BINDERS_AND_ELLIPSES: &[Accepted] = &[
    Accepted {
        source: "def bb1 α [Inhabited α] : α := default",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bb1 []) (Command.optDeclSig [`α (Term.instBinder "[" [] (Term.app `Inhabited [`α]) "]")] [(Term.typeSpec ":" `α)]) (Command.declValSimple ":=" `default (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "abbrev bb2 α β := α × β",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.abbrev "abbrev" (Command.declId `bb2 []) (Command.optDeclSig [`α `β] []) (Command.declValSimple ":=" («term_×_» `α "×" `β) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def bb3 (n : Nat) : Nat :=\n  match n with\n  | .succ .. => 1\n  | .zero => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bb3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `succ) [(Term.ellipsis "..")])]] "=>" (num "1")) (Term.matchAlt "|" [[(Term.dotIdent "." `zero)]] "=>" (num "0"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def bb4 (o : Option (Nat × Nat)) : Nat :=\n  match o with\n  | some (.mk ..) => 1\n  | none => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bb4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app (Term.dotIdent "." `mk) [(Term.ellipsis "..")]) ")")])]] "=>" (num "1")) (Term.matchAlt "|" [[`none]] "=>" (num "0"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def bb5 (n : Nat) : Nat :=\n  let f x := x + 1\n  f n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bb5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `f) [`x] [] ":=" («term_+_» `x "+" (num "1")))) [] (Term.app `f [`n])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def bb7 : Nat → Nat := fun x => x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bb7 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`x] [] "=>" `x)) (Termination.suffix [] []) []) []))"#,
    },
];

/// Dependent arrows (`leading_parser:25`) start only where the right side is at precedence 25 or
/// below: `a ∈ [b] → c` is `(a ∈ [b]) → c` with a list, `f [1]` passes a list, while
/// `(α : Type) → [Inhabited α] → α` and `p → [C] → q` keep their binders.
const ARROW_POSITIONS: &[Accepted] = &[
    Accepted {
        source: "theorem ar1 {a b : Nat} : a ∈ [b] → a = b := by\n  intro h\n  cases h <;> trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ar1 []) (Command.declSig [(Term.implicitBinder "{" [`a `b] [":" `Nat] "}")] (Term.typeSpec ":" (Term.arrow («term_∈_» `a "∈" («term[_]» "[" [`b] "]")) "→" («term_=_» `a "=" `b)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intro "intro" [`h]) [] (Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `h)] [] []) "<;>" (Tactic.tacticTrivial "trivial"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ar2 : ∀ (α : Type) [Inhabited α] (x : α), x = x := fun _ _ _ => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ar2 []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [])] [] ")") (Term.instBinder "[" [] (Term.app `Inhabited [`α]) "]") (Term.explicitBinder "(" [`x] [":" `α] [] ")")] [] "," («term_=_» `x "=" `x)))) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_") (Term.hole "_")] [] "=>" `rfl)) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def ar3 : (α : Type) → [Inhabited α] → α := fun _ _ => default",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ar3 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.depArrow (Term.explicitBinder "(" [`α] [":" (Term.type "Type" [])] [] ")") "→" (Term.depArrow (Term.instBinder "[" [] (Term.app `Inhabited [`α]) "]") "→" `α)))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `default)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem ar4 (p : Prop) : p → [Inhabited Nat] → p := fun h _ => h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ar4 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow `p "→" (Term.depArrow (Term.instBinder "[" [] (Term.app `Inhabited [`Nat]) "]") "→" `p)))) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`h (Term.hole "_")] [] "=>" `h)) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def ar5 (f : List Nat → Nat) : Nat := f [1] + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ar5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow (Term.app `List [`Nat]) "→" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (Term.app `f [(«term[_]» "[" [(num "1")] "]")]) "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem ar6 (p q : Prop) : (p ∧ q) → (h : p) → p := fun _ h => h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ar6 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_∧_» `p "∧" `q) ")") "→" (Term.depArrow (Term.explicitBinder "(" [`h] [":" `p] [] ")") "→" `p)))) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_") `h] [] "=>" `h)) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem eq_of_mem_singleton {a b : Nat} : a ∈ [b] → a = b\n  | .head .. => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `eq_of_mem_singleton []) (Command.declSig [(Term.implicitBinder "{" [`a `b] [":" `Nat] "}")] (Term.typeSpec ":" (Term.arrow («term_∈_» `a "∈" («term[_]» "[" [`b] "]")) "→" («term_=_» `a "=" `b)))) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `head) [(Term.ellipsis "..")])]] "=>" `rfl)]) (Termination.suffix [] []) []))))"#,
    },
];

/// The tactic `open openDecl in tacs` (`Tactic.open`), its declaration in the forms of the command,
/// its sequence on the same line or on its own (positioned at its first token).
const TACTIC_OPENS: &[Accepted] = &[
    Accepted {
        source: "theorem oi1 (n : Nat) : n = n := by\n  open Nat in rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `oi1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.open "open" (Command.openSimple [`Nat]) "in" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem oi2 (n : Nat) : n = n := by\n  open Nat hiding add in\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `oi2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.open "open" (Command.openHiding `Nat "hiding" [`add]) "in" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem oi3 (n : Nat) : n + 0 = n := by\n  open Nat (add_zero) in simp [add_zero]; done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `oi3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.open "open" (Command.openOnly `Nat "(" [`add_zero] ")") "in" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `add_zero)] "]"] []) ";" (Tactic.done "done")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem oi4 (n : Nat) : n = n := by\n  skip\n  open scoped Nat in rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `oi4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip") [] (Tactic.open "open" (Command.openScoped "scoped" [`Nat]) "in" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A `by` owns the `<;>`s after it: `suffices h : t by⏎ … split <;> simp` and `exact by skip <;> …`
/// keep the chain inside the proof, never around the whole tactic.
const BY_OWNED_CHAINS: &[Accepted] = &[
    Accepted {
        source: "theorem sb3 (a b : Nat) : min a b = min a b := by\n  suffices min_eq : min a b = if a ≤ b then a else b by\n    rfl\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sb3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `min [`a `b]) "=" (Term.app `min [`a `b])))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSuffices_ "suffices" (Term.sufficesDecl (group `min_eq ":") («term_=_» (Term.app `min [`a `b]) "=" (termIfThenElse "if" («term_≤_» `a "≤" `b) "then" `a "else" `b)) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem sb4 (a b : Nat) : min a b = min a b := by\n  open Nat in\n  suffices min_eq : min a b = if a ≤ b then a else b by\n    rfl\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sb4 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `min [`a `b]) "=" (Term.app `min [`a `b])))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.open "open" (Command.openSimple [`Nat]) "in" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSuffices_ "suffices" (Term.sufficesDecl (group `min_eq ":") («term_=_» (Term.app `min [`a `b]) "=" (termIfThenElse "if" («term_≤_» `a "≤" `b) "then" `a "else" `b)) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))))) [] (Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "public instance {α : Type u} [LE α] [Min α] [LawfulOrderLeftLeaningMin α] :\n    MinEqOr α where\n  min_eq_or a b := by\n    open scoped Classical in\n    suffices min_eq : min a b = if a ≤ b then a else b by\n      rw [min_eq]\n      split <;> simp\n    split <;> simp [*, LawfulOrderLeftLeaningMin.min_eq_left, LawfulOrderLeftLeaningMin.min_eq_right]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.public "public")] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [`u])] "}") (Term.instBinder "[" [] (Term.app `LE [`α]) "]") (Term.instBinder "[" [] (Term.app `Min [`α]) "]") (Term.instBinder "[" [] (Term.app `LawfulOrderLeftLeaningMin [`α]) "]")] (Term.typeSpec ":" (Term.app `MinEqOr [`α]))) (Command.whereStructInst "where" (Term.structInstFields [(Term.structInstField (Term.structInstLVal `min_eq_or []) [[`a `b] [] (Term.structInstFieldDef ":=" [] (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.open "open" (Command.openScoped "scoped" [`Classical]) "in" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSuffices_ "suffices" (Term.sufficesDecl (group `min_eq ":") («term_=_» (Term.app `min [`a `b]) "=" (termIfThenElse "if" («term_≤_» `a "≤" `b) "then" `a "else" `b)) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `min_eq)] "]") []) [] (Tactic.«tactic_<;>_» (Tactic.split "split" [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))]))))) [] (Tactic.«tactic_<;>_» (Tactic.split "split" [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpStar "*") "," (Tactic.simpLemma [] [] `LawfulOrderLeftLeaningMin.min_eq_left) "," (Tactic.simpLemma [] [] `LawfulOrderLeftLeaningMin.min_eq_right)] "]"] []))])))]))))])]) [])))"#,
    },
    Accepted {
        source: "theorem ch1 (p : Prop) (hp : p) : p := by\n  exact by skip <;> exact hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ch1 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")")] (Term.typeSpec ":" `p)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.skip "skip") "<;>" (Tactic.exact "exact" `hp))]))))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem sx (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  suffices h : q by\n    constructor <;> first | exact hp | exact h\n  exact hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sx []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSuffices_ "suffices" (Term.sufficesDecl (group `h ":") `q (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.first "first" [(group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) (group "|" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h)])))]))]))))) [] (Tactic.exact "exact" `hq)]))) (Termination.suffix [] []) [])))"#,
    },
];

/// The bounded ranges are `syntax:max (term "...=" term)`: they take only the operand before them
/// (`a ∈ lo...=hi` is `a ∈ (lo...=hi)`) and a whole term after (`1...n + 1`).
const RANGE_POSITIONS: &[Accepted] = &[
    Accepted {
        source: "theorem rg1 (a lo hi : Nat) : (a ∈ lo...=hi) = (a ∈ lo...=hi) := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `rg1 []) (Command.declSig [(Term.explicitBinder "(" [`a `lo `hi] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_∈_» `a "∈" (Std.«term_...=_» `lo "...=" `hi)) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_∈_» `a "∈" (Std.«term_...=_» `lo "...=" `hi)) ")")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem rg2 (a lo hi : Nat) : (a ∈ (Nat.succ lo)...=(Nat.succ hi)) ↔ a ∈ lo...=hi := Iff.rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `rg2 []) (Command.declSig [(Term.explicitBinder "(" [`a `lo `hi] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_↔_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_∈_» `a "∈" (Std.«term_...=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Nat.succ [`lo]) ")") "...=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Nat.succ [`hi]) ")"))) ")") "↔" («term_∈_» `a "∈" (Std.«term_...=_» `lo "...=" `hi))))) (Command.declValSimple ":=" `Iff.rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def rg3 (n : Nat) : List Nat := (0...n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `rg3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_..._» (num "0") "..." `n) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def rg4 (n : Nat) : List Nat := (1...n + 1).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `rg4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_..._» (num "1") "..." («term_+_» `n "+" (num "1"))) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def rg5 (n : Nat) : List Nat := (0...<n).toList ++ (0...=n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `rg5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" («term_++_» (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_...<_» (num "0") "...<" `n) ")") "." `toList) "++" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_...=_» (num "0") "...=" `n) ")") "." `toList)) (Termination.suffix [] []) []) []))"#,
    },
];

/// A binder default in a dependent arrow or a `∀` (`(h : i = i := by rfl) → Nat`,
/// `∀ (j : Nat := 3), …`): `explicitBinder`'s `binderTactic <|> binderDefault` after the type.
const TERM_BINDER_DEFAULTS: &[Accepted] = &[
    Accepted {
        source: "def bt1 (n : Nat) (h : n = n := by rfl) : Nat := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bt1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `n "=" `n)] [(Term.binderTactic ":=" "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def bt2 : (i : Nat) → (h : i = i := by rfl) → Nat := fun i _ => i",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bt2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.depArrow (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") "→" (Term.depArrow (Term.explicitBinder "(" [`h] [":" («term_=_» `i "=" `i)] [(Term.binderTactic ":=" "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))] ")") "→" `Nat)))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`i (Term.hole "_")] [] "=>" `i)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem bt4 : ∀ (i : Nat) (h : i = i := by rfl), i = i := fun _ h => h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bt4 []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `i "=" `i)] [(Term.binderTactic ":=" "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))] ")")] [] "," («term_=_» `i "=" `i)))) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_") `h] [] "=>" `h)) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def bt5 : (i : Nat) → (j : Nat := 3) → Nat := fun i j => i + j",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bt5 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.depArrow (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") "→" (Term.depArrow (Term.explicitBinder "(" [`j] [":" `Nat] [(Term.binderDefault ":=" (num "3"))] ")") "→" `Nat)))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`i `j] [] "=>" («term_+_» `i "+" `j))) (Termination.suffix [] []) []) []))"#,
    },
];

/// A structure or class after `declModifiers` (`private`, `@[ext]`, `public`), its fields indented
/// past the command's start, not past the keyword.
const STRUCTURE_MODIFIERS: &[Accepted] = &[
    Accepted {
        source: "private structure SM1 where\n  x : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `SM1 []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "@[ext] structure SM2 where\n  x : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.ext "ext" [] [] []))] "]")] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `SM2 []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "structure SM3 (α : Type) where\n  a : α",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `SM3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [])] [] ")")] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `a (Command.optDeclSig [] [(Term.typeSpec ":" `α)]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "structure SM4 where\n  y : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `SM4 []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `y (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "public class SM5 (α : Type) where\n  op : α → α",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.public "public")] [] [] [] []) (Command.structure (Command.classTk "class") (Command.declId `SM5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [])] [] ")")] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `op (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `α "→" `α))]) [])])] (Command.optDeriving [])))"#,
    },
];

/// `show T by tac` and `show T from e` whose `T` opens with a prefix operator (`show ¬k = 0 by …`):
/// the operand is folded before the `by` closes the annotation.
const SHOW_AFTER_PREFIX: &[Accepted] = &[
    Accepted {
        source: "theorem sh1 (k : Nat) (h : k = 0) : k = 0 := show k = 0 by exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sh1 []) (Command.declSig [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `k "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» `k "=" (num "0")))) (Command.declValSimple ":=" (Term.show "show" («term_=_» `k "=" (num "0")) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h)])))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem sh2 (k : Nat) (h : k ≠ 0) : ¬k = 0 := show ¬k = 0 by exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sh2 []) (Command.declSig [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_≠_» `k "≠" (num "0"))] [] ")")] (Term.typeSpec ":" («term¬_» "¬" («term_=_» `k "=" (num "0"))))) (Command.declValSimple ":=" (Term.show "show" («term¬_» "¬" («term_=_» `k "=" (num "0"))) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h)])))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem sh3 (k : Nat) (h : k ≠ 0) : ¬k = 0 := show ¬(k = 0) by exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sh3 []) (Command.declSig [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_≠_» `k "≠" (num "0"))] [] ")")] (Term.typeSpec ":" («term¬_» "¬" («term_=_» `k "=" (num "0"))))) (Command.declValSimple ":=" (Term.show "show" («term¬_» "¬" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_=_» `k "=" (num "0")) ")")) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h)])))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem sh4 (k : Nat) (h : k ≠ 0) : ¬k = 0 := show ¬k = 0 from h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `sh4 []) (Command.declSig [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_≠_» `k "≠" (num "0"))] [] ")")] (Term.typeSpec ":" («term¬_» "¬" («term_=_» `k "=" (num "0"))))) (Command.declValSimple ":=" (Term.show "show" («term¬_» "¬" («term_=_» `k "=" (num "0"))) (Term.fromTerm "from" `h)) (Termination.suffix [] []) [])))"#,
    },
];

/// `·` heading an application inside its parentheses (`(· trivial)`, `(· 1) f`).
const CDOT_HEADS: &[Accepted] = &[
    Accepted {
        source: "def ch1 : (True → Prop) → Prop := (· trivial)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ch1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow `True "→" (Term.prop "Prop")) ")") "→" (Term.prop "Prop")))]) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app (Term.cdot "·" (hygieneInfo `[anonymous])) [`trivial]) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ch2 (f : Nat → Nat) : Nat := (· 1) f",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ch2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app (Term.cdot "·" (hygieneInfo `[anonymous])) [(num "1")]) ")") [`f]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem ch3 : (True → True) ↔ True := ⟨(· trivial), (fun _ => ·)⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ch3 []) (Command.declSig [] (Term.typeSpec ":" («term_↔_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow `True "→" `True) ")") "↔" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app (Term.cdot "·" (hygieneInfo `[anonymous])) [`trivial]) ")") "," (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.cdot "·" (hygieneInfo `[anonymous])))) ")")] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// A structure field `h : T := by tac`: `binderTactic` (an `autoParam` field), not a default value.
const FIELD_TACTIC_DEFAULTS: &[Accepted] = &[Accepted {
    source: "structure BT3 where\n  x : Nat\n  h : x = x := by rfl",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `BT3 []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) []) (Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `h (Command.optDeclSig [] [(Term.typeSpec ":" («term_=_» `x "=" `x))]) [(Term.binderTactic ":=" "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])])] (Command.optDeriving [])))"#,
}];

/// `variable … in`, `include … in` and `omit … in` (`omit` with names or instance binders):
/// `Command.in`, the head read up to its `in`.
const SCOPE_IN_COMMANDS: &[Accepted] = &[
    Accepted {
        source: "omit [BEq α] in theorem si1 (a : α) : a = a := rfl",
        tree: r#"(Command.in (Command.omit "omit" [(Term.instBinder "[" [] (Term.app `BEq [`α]) "]")]) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `si1 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `α] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) []))))"#,
    },
    Accepted {
        source: "variable (β : Type) in theorem si2 (b : β) : b = b := rfl",
        tree: r#"(Command.in (Command.variable "variable" [(Term.explicitBinder "(" [`β] [":" (Term.type "Type" [])] [] ")")]) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `si2 []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `β] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `b))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) []))))"#,
    },
    Accepted {
        source: "include α in theorem si3 : True := trivial",
        tree: r#"(Command.in (Command.include "include" [`α]) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `si3 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) []))))"#,
    },
    Accepted {
        source: "omit [Inhabited α] [BEq α] in theorem si4 (a : α) : a = a := rfl",
        tree: r#"(Command.in (Command.omit "omit" [(Term.instBinder "[" [] (Term.app `Inhabited [`α]) "]") (Term.instBinder "[" [] (Term.app `BEq [`α]) "]")]) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `si4 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `α] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `a))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) []))))"#,
    },
    Accepted {
        source: "omit h in theorem si5 : True := trivial",
        tree: r#"(Command.in (Command.omit "omit" [`h]) "in" (Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `si5 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) []))))"#,
    },
];

/// `calc`: `Lean.calc "calc" (calcSteps (calcFirstStep r (":=" p)?) calcStep*)` (`Lean.calcTactic` as a
/// tactic), the steps after the first at a position of their own.
const CALCULATIONS: &[Accepted] = &[
    Accepted {
        source: "theorem c1 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=\n  calc a = b := h1\n    _ = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Lean.calc "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)])) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c2 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=\n  calc\n    a = b := h1\n    _ = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Lean.calc "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)])) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c3 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc\n    a = b := h1\n    _ = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.calcTactic "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c4 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  exact calc a = b := h1\n    _ = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c4 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Lean.calc "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c5 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc a = b := h1\n    _ = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c5 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.calcTactic "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c7 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=\n  calc\n      a = b := h1\n    _ = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c7 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Lean.calc "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)])) (Termination.suffix [] []) [])))"#,
    },
];

/// Alternatives sharing a right-hand side (`| 0 | 1 => 0`, across lines too): `matchAlt`'s
/// pattern groups separated by `|`.
const SHARED_ALTERNATIVES: &[Accepted] = &[
    Accepted {
        source: "def sa1 : Nat → Nat\n  | 0 | 1 => 0\n  | _ => 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sa1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(num "0")] "|" [(num "1")]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" (num "1"))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def sa2 (o : Option Nat) : Nat :=\n  match o with | none | some 0 => 0 | some _ => 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sa2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[`none] "|" [(Term.app `some [(num "0")])]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.app `some [(Term.hole "_")])]] "=>" (num "1"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sa3 (o : Option Nat) : Nat :=\n  match o with\n  | none | some 0 => 0\n  | some _ => 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sa3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[`none] "|" [(Term.app `some [(num "0")])]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.app `some [(Term.hole "_")])]] "=>" (num "1"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sa4 : Option Nat → Nat\n  | .some .. | .none => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sa4 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.app `Option [`Nat]) "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `some) [(Term.ellipsis "..")])] "|" [(Term.dotIdent "." `none)]] "=>" (num "0"))]) (Termination.suffix [] []) [])) []))"#,
    },
];

/// An `rcases` target's name (`rcases h : b with …`, a `binderIdent`) and the `coe` attribute
/// (`Lean.Attr.coe`).
const RCASES_NAMES_AND_COE: &[Accepted] = &[
    Accepted {
        source: "theorem rn (b : Bool) : b = b := by\n  rcases h : b with rfl | rfl\n  · rfl\n  · rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `rn []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rcases "rcases" [(Tactic.elimTarget [(Lean.binderIdent `h) ":"] `b)] ["with" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl) "|" (Tactic.rcasesPat.one `rfl)]) [])]) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[coe] def toIntCoe (n : Nat) : Int := n",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Lean.Attr.coe "coe"))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `toIntCoe []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Int)]) (Command.declValSimple ":=" `n (Termination.suffix [] []) []) []))"#,
    },
];

/// `let mut x := e` (`doLet`'s `mut` slot), `let mut x ← a`, and the reassignments `x := e` (`doReassign`,
/// `letIdDeclNoBinders`) and `x ← a` (`doReassignArrow`), last in a loop body too.
const MUTABLE_DO_VARIABLES: &[Accepted] = &[
    Accepted {
        source: "def lm1 (n : Nat) : Id Nat := do\n  let mut x := n\n  x := x + 1\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lm1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [] ":=" `n))) []) (Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `x) [] [] ":=" («term_+_» `x "+" (num "1")))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lm2 (n : Nat) : Nat := Id.run do\n  let mut x := n\n  x := x + 1\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lm2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [] ":=" `n))) []) (Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `x) [] [] ":=" («term_+_» `x "+" (num "1")))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lm3 (n : Nat) : Nat := Id.run do\n  let mut x : Nat := n\n  for i in [1, 2] do\n    x := x + i\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lm3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [(Term.typeSpec ":" `Nat)] ":=" `n))) []) (Term.doSeqItem (Term.doFor "for" [(Term.doForDecl [] `i "in" («term[_]» "[" [(num "1") "," (num "2")] "]"))] "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `x) [] [] ":=" («term_+_» `x "+" `i))) [])])) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lm4 (n : Nat) (act : Id Nat) : Id Nat := do\n  let mut x ← act\n  x ← act\n  x := x + n\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lm4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`act] [":" (Term.app `Id [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" ["mut"] (Term.letConfig []) (Term.doIdDecl `x [] "←" (Term.doExpr `act))) []) (Term.doSeqItem (Term.doReassignArrow (Term.doIdDecl `x [] "←" (Term.doExpr `act))) []) (Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `x) [] [] ":=" («term_+_» `x "+" `n))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lm5 (n : Nat) : Nat := Id.run do\n  let mut x : Nat := n\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lm5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [(Term.typeSpec ":" `Nat)] ":=" `n))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lm6 (n : Nat) : Nat := Id.run do\n  let mut x := n\n  for i in [1, 2] do\n    x := x + i\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lm6 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [] ":=" `n))) []) (Term.doSeqItem (Term.doFor "for" [(Term.doForDecl [] `i "in" («term[_]» "[" [(num "1") "," (num "2")] "]"))] "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `x) [] [] ":=" («term_+_» `x "+" `i))) [])])) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
];

/// A bounded range after an application's last argument takes only that argument and the rest of
/// the group: `f range 0...<xs.size` is `f range (0...<xs.size)`.
const RANGE_ARGUMENTS: &[Accepted] = &[
    Accepted {
        source: "def ra1 (xs : Array Nat) (f : Nat → Std.Rco Nat → Nat) (range : Nat) : Nat := f range 0...<xs.size",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ra1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" (Term.arrow (Term.app `Std.Rco [`Nat]) "→" `Nat))] [] ")") (Term.explicitBinder "(" [`range] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `f [`range (Std.«term_...<_» (num "0") "...<" `xs.size)]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ra2 (f : Std.Rco Nat → Nat) (n : Nat) : Nat := f 0...<n + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ra2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow (Term.app `Std.Rco [`Nat]) "→" `Nat)] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `f [(Std.«term_...<_» (num "0") "...<" («term_+_» `n "+" (num "1")))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ra3 (n : Nat) : List Nat := (0...<n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ra3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term_...<_» (num "0") "...<" `n) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
];

/// Constructor docs and visibility: `structCtor`'s `declModifiers` (`/-- … -/ mk ::`, `private mk ::`)
/// and a doc before a `|` of an `inductive` without `where`.
const CONSTRUCTOR_DOC_LAYOUTS: &[Accepted] = &[
    Accepted {
        source: "structure CD1 where\n  /-- The constructor. -/\n  mk ::\n  x : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `CD1 []) (Command.optDeclSig [] []) [] ["where" [(Command.structCtor (Command.declModifiers [(Command.docComment "/--" "The constructor. -/")] [] [] [] [] [] []) `mk [] "::")] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "structure CD2 where\n  private mk ::\n  x : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `CD2 []) (Command.optDeclSig [] []) [] ["where" [(Command.structCtor (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) `mk [] "::")] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "inductive CD3\n  /-- One. -/\n  | one\n  /-- Two. -/\n  | two",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `CD3 []) (Command.optDeclSig [] []) [] [(Command.ctor [(Command.docComment "/--" "One. -/")] "|" (Command.declModifiers [] [] [] [] [] [] []) `one (Command.optDeclSig [] [])) (Command.ctor [(Command.docComment "/--" "Two. -/")] "|" (Command.declModifiers [] [] [] [] [] [] []) `two (Command.optDeclSig [] []))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "inductive CD4\n  | one\n  | two",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `CD4 []) (Command.optDeclSig [] []) [] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `one (Command.optDeclSig [] [])) (Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `two (Command.optDeclSig [] []))] [] (Command.optDeriving [])))"#,
    },
];

/// A `do` `if` whose `else` holds just an `if`: the pin's `doIf` else-if clauses
/// (`group (group "else" "if") cond "then" seq`), the inner clauses and `else` moved up.
const DO_ELSE_IF: &[Accepted] = &[
    Accepted {
        source: "def de1 (n : Nat) : Id Nat := do\n  if n = 0 then\n    return 1\n  else if n = 1 then\n    return 2\n  else\n    return 3",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `de1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doIf "if" (Term.doIfProp [] («term_=_» `n "=" (num "0"))) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [(num "1")]) [])]) [(group (group "else" "if") (Term.doIfProp [] («term_=_» `n "=" (num "1"))) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [(num "2")]) [])]))] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [(num "3")]) [])])]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def de2 (n : Nat) : Id Nat := do\n  if n = 0 then return 1 else if n = 1 then return 2 else return 3",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `de2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doIf "if" (Term.doIfProp [] («term_=_» `n "=" (num "0"))) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [(num "1")]) [])]) [(group (group "else" "if") (Term.doIfProp [] («term_=_» `n "=" (num "1"))) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [(num "2")]) [])]))] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [(num "3")]) [])])]) [])])) (Termination.suffix [] []) []) []))"#,
    },
];

/// An `instance … where` with no field (`structInstFields []`).
const EMPTY_WHERE_INSTANCES: &[Accepted] = &[
    Accepted {
        source: "class EW1 (α : Type) where\n  x : Nat := 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.classTk "class") (Command.declId `EW1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [])] [] ")")] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [(Term.binderDefault ":=" (num "1"))])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "instance : EW1 Nat where",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `EW1 [`Nat]))) (Command.whereStructInst "where" (Term.structInstFields []) [])))"#,
    },
    Accepted {
        source: "def ew2 : Nat := (inferInstance : EW1 Nat).x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ew2 []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.proj (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `inferInstance ":" [(Term.app `EW1 [`Nat])] ")") "." `x) (Termination.suffix [] []) []) []))"#,
    },
];

/// A local defined by equations: `letEqnsDecl` (`let rec go : T | p => e | …`, `let f : T | …`), its
/// type ending at the first `|`.
const LOCAL_EQUATIONS: &[Accepted] = &[
    Accepted {
        source: "def le1 (n : Nat) : Nat :=\n  let rec go : Nat → Nat\n    | 0 => 0\n    | k + 1 => go k + 1\n  go n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `le1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letEqnsDecl (Term.letId `go) [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))] (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `k "+" (num "1"))]] "=>" («term_+_» (Term.app `go [`k]) "+" (num "1")))]))) (Termination.suffix [] []))]) [] (Term.app `go [`n])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def le2 (n : Nat) : Nat :=\n  let f : Nat → Nat\n    | 0 => 1\n    | _ => 2\n  f n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `le2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letEqnsDecl (Term.letId `f) [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))] (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "1")) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" (num "2"))]))) [] (Term.app `f [`n])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "@[inline] def foldM2 {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) : m α :=\n  let rec @[specialize] loop : ∀ i, i ≤ n → α → m α\n    | 0,   h, a => pure a\n    | i+1, h, a => f (n-i-1) (by omega) a >>= loop i (Nat.le_of_succ_le h)\n  loop n (by omega) init",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `inline []))] "]")] [] [] [] [] []) (Command.definition "def" (Command.declId `foldM2 []) (Command.optDeclSig [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [`u])] "}") (Term.implicitBinder "{" [`m] [":" (Term.arrow (Term.type "Type" [`u]) "→" (Term.type "Type" [`v]))] "}") (Term.instBinder "[" [] (Term.app `Monad [`m]) "]") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`f] [":" (Term.depArrow (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") "→" (Term.arrow («term_<_» `i "<" `n) "→" (Term.arrow `α "→" (Term.app `m [`α]))))] [] ")") (Term.explicitBinder "(" [`init] [":" `α] [] ")")] [(Term.typeSpec ":" (Term.app `m [`α]))]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.specialize "specialize" []))] "]")] (Term.letDecl (Term.letEqnsDecl (Term.letId `loop) [] [(Term.typeSpec ":" (Term.forall "∀" [`i] [] "," (Term.arrow («term_≤_» `i "≤" `n) "→" (Term.arrow `α "→" (Term.app `m [`α])))))] (Term.matchAlts [(Term.matchAlt "|" [[(num "0") "," `h "," `a]] "=>" (Term.app `pure [`a])) (Term.matchAlt "|" [[(«term_+_» `i "+" (num "1")) "," `h "," `a]] "=>" («term_>>=_» (Term.app `f [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» («term_-_» `n "-" `i) "-" (num "1")) ")") (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) ")") `a]) ">>=" (Term.app `loop [`i (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Nat.le_of_succ_le [`h]) ")")])))]))) (Termination.suffix [] []))]) [] (Term.app `loop [`n (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) ")") `init])) (Termination.suffix [] []) []) []))"#,
    },
];

/// A term `if let p := e then a else b` (`termIfLet`).
const TERM_IF_LET: &[Accepted] = &[
    Accepted {
        source: "def til1 (o : Option Nat) : Nat :=\n  if let some n := o then n else 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `til1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfLet "if" "let" (Term.app `some [`n]) ":=" `o "then" `n "else" (num "0")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def til2 (o : Option Nat) (b : Bool) : Nat :=\n  if let some n := o then\n    n\n  else if b then\n    1\n  else\n    0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `til2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")") (Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfLet "if" "let" (Term.app `some [`n]) ":=" `o "then" `n "else" (termIfThenElse "if" `b "then" (num "1") "else" (num "0"))) (Termination.suffix [] []) []) []))"#,
    },
];

/// `induction l with simp_all` (a pre-tactic and no alternative, `inductionAlts "with" [tac] []`) and
/// the root-namespace tactic `get_elem_tactic` (`tacticGet_elem_tactic`).
const WITH_ONLY_ELIMINATIONS: &[Accepted] = &[
    Accepted {
        source: "theorem wo1 (l : List Nat) : l = l := by\n  induction l with simp_all",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `wo1 []) (Command.declSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» `l "=" `l))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `l)] [] [] [(Tactic.inductionAlts "with" [(Tactic.simpAll "simp_all" (Tactic.optConfig []) [] [] [])] [])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem wo2 (xs : Array Nat) (i : Nat) (h : i < xs.size := by get_elem_tactic) : xs[i] = xs[i] := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `wo2 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» `i "<" `xs.size)] [(Term.binderTactic ":=" "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticGet_elem_tactic "get_elem_tactic")])))] ")")] (Term.typeSpec ":" («term_=_» («term__[_]» `xs "[" `i "]") "=" («term__[_]» `xs "[" `i "]")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem wo3 (n : Nat) : n = n := by\n  induction n with simp\n  | zero => rfl\n  | succ k ih => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `wo3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] [] [] [(Tactic.inductionAlts "with" [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `succ) [`k `ih])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem wo4 (n : Nat) : n = n := by\n  cases n with rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `wo4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] [(Tactic.inductionAlts "with" [(Tactic.tacticRfl "rfl")] [])])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A term `let` with a pattern (`letPatDecl`: `let ⟨a, b⟩ := p`, `let (a, b) := p`).
const TERM_PATTERN_LETS: &[Accepted] = &[
    Accepted {
        source: "def lp1 (p : Nat × Nat) : Nat :=\n  let ⟨a, b⟩ := p\n  a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lp1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`a "," `b] "⟩") [] [] ":=" `p)) [] («term_+_» `a "+" `b)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lp2 (p : Nat × Nat) : Nat :=\n  let (a, b) := p\n  a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lp2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") [] [] ":=" `p)) [] («term_+_» `a "+" `b)) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem lp1_ok : lp1 (2, 3) = 5 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `lp1_ok []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.app `lp1 [(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(num "2") "," [(num "3")]] ")")]) "=" (num "5")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
];

/// A branch's destructuring `let` (`letPatDecl`, in an `if` branch and in match alternatives,
/// with and without a type), and a type ascription without its type (`(e :)`, `typeAscription`'s
/// optional type). Captured 2026-10-09 from one file the pin elaborated without a message, in this
/// order.
const BRANCH_PATTERN_LETS_AND_BARE_ASCRIPTIONS: &[Accepted] = &[
    Accepted {
        source: "def bp1 (p : Nat × Nat) (b : Bool) : Nat :=\n  if b then\n    let ⟨x, y⟩ := p\n    x + y\n  else 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bp1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")") (Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termIfThenElse "if" `b "then" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `y] "⟩") [] [] ":=" `p)) [] («term_+_» `x "+" `y)) "else" (num "0")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def bp2 (o : Option (Nat × Nat)) : Nat :=\n  match o with\n  | some q =>\n    let ⟨x, y⟩ := q\n    x + y\n  | none => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bp2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [`q])]] "=>" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `y] "⟩") [] [] ":=" `q)) [] («term_+_» `x "+" `y))) (Term.matchAlt "|" [[`none]] "=>" (num "0"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def bp3 (o : Option (Nat × Nat)) : Nat :=\n  match o with\n  | some q => let ⟨x, y⟩ : Nat × Nat := q; x + y\n  | none => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `bp3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [`q])]] "=>" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`x "," `y] "⟩") [] [(Term.typeSpec ":" («term_×_» `Nat "×" `Nat))] ":=" `q)) ";" («term_+_» `x "+" `y))) (Term.matchAlt "|" [[`none]] "=>" (num "0"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ba1 (n : Nat) : Nat := (n + 1 :)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ba1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `n "+" (num "1")) ":" [] ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem ba2 (a b : Nat) (h : a = b) : b = a := (h.symm :)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ba2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `h.symm ":" [] ")") (Termination.suffix [] []) [])))"#,
    },
];

/// `intro`'s `term:max` arguments, bracketed patterns included (`intro h ⟨h₁, h₂⟩`,
/// `intro (k : Fin 1)`); `rintro`'s parenthesized units, `rintroPat.binder` (`(hp hq)`,
/// `(h : P)`) or, with alternatives, `rcasesPat.paren` (`(h | h)`); a tactic `have`/`let`'s
/// binders (`have H (k : Nat) : …`, `have (k : Nat) : …`, `let f x y := …`) and `_` as its name.
/// Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const INTRO_PATTERNS_AND_LOCAL_BINDERS: &[Accepted] = &[
    Accepted {
        source: "theorem i1 (P Q R : Prop) : (P → Q → R) → (P ∧ Q → R) := by intro h ⟨h₁, h₂⟩; exact h h₁ h₂",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `i1 []) (Command.declSig [(Term.explicitBinder "(" [`P `Q `R] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow `P "→" (Term.arrow `Q "→" `R)) ")") "→" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow («term_∧_» `P "∧" `Q) "→" `R) ")")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intro "intro" [`h (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]) ";" (Tactic.exact "exact" (Term.app `h [`h₁ `h₂]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem i2 : ∀ (k : Fin 1), k = k := by\n  intro (k : Fin 1)\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `i2 []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [(Term.explicitBinder "(" [`k] [":" (Term.app `Fin [(num "1")])] [] ")")] [] "," («term_=_» `k "=" `k)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intro "intro" [(Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `k ":" [(Term.app `Fin [(num "1")])] ")")]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem i3 (p : Nat × Nat → Prop) (h : ∀ a b, p (a, b)) : ∀ x, p x := by\n  intro ⟨a, b⟩\n  exact h a b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `i3 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.arrow («term_×_» `Nat "×" `Nat) "→" (Term.prop "Prop"))] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`a `b] [] "," (Term.app `p [(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")")]))] [] ")")] (Term.typeSpec ":" (Term.forall "∀" [`x] [] "," (Term.app `p [`x])))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intro "intro" [(Term.anonymousCtor "⟨" [`a "," `b] "⟩")]) [] (Tactic.exact "exact" (Term.app `h [`a `b]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem r1 (a b : Nat) : a = 0 ∨ a = b → a = a := by\n  rintro (h | h) <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" (Term.arrow («term_∨_» («term_=_» `a "=" (num "0")) "∨" («term_=_» `a "=" `b)) "→" («term_=_» `a "=" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.rintro "rintro" [(Tactic.rintroPat.one (Tactic.rcasesPat.paren "(" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h) "|" (Tactic.rcasesPat.one `h)]) []) ")"))] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem r2 (P Q : Prop) : P ∧ Q ∨ Q ∧ P → Q := by\n  rintro (⟨-, hq⟩ | ⟨hq, -⟩) <;> exact hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r2 []) (Command.declSig [(Term.explicitBinder "(" [`P `Q] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow («term_∨_» («term_∧_» `P "∧" `Q) "∨" («term_∧_» `Q "∧" `P)) "→" `Q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.rintro "rintro" [(Tactic.rintroPat.one (Tactic.rcasesPat.paren "(" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hq)]) [])] "⟩") "|" (Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hq)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])] "⟩")]) []) ")"))] []) "<;>" (Tactic.exact "exact" `hq))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem r3 (P : Prop) : P → P := by\n  rintro (h : P)\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r3 []) (Command.declSig [(Term.explicitBinder "(" [`P] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow `P "→" `P))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rintro "rintro" [(Tactic.rintroPat.binder "(" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `h))] [":" `P] ")")] []) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem r4 (P Q : Prop) : P → Q → P := by\n  rintro (hp hq)\n  exact hp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `r4 []) (Command.declSig [(Term.explicitBinder "(" [`P `Q] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.arrow `P "→" (Term.arrow `Q "→" `P)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rintro "rintro" [(Tactic.rintroPat.binder "(" [(Tactic.rintroPat.one (Tactic.rcasesPat.one `hp)) (Tactic.rintroPat.one (Tactic.rcasesPat.one `hq))] [] ")")] []) [] (Tactic.exact "exact" `hp)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h1 (n : Nat) : n + 0 = n := by\n  have H (k : Nat) : k + 0 = k := Nat.add_zero k\n  exact H n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `H) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_=_» («term_+_» `k "+" (num "0")) "=" `k))] ":=" (Term.app `Nat.add_zero [`k])))) [] (Tactic.exact "exact" (Term.app `H [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h2 (n : Nat) : n + 0 = n := by\n  have (k : Nat) : k + 0 = k := Nat.add_zero k\n  exact this n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_=_» («term_+_» `k "+" (num "0")) "=" `k))] ":=" (Term.app `Nat.add_zero [`k])))) [] (Tactic.exact "exact" (Term.app `this [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h3 (n : Nat) : n + 0 = n := by\n  have H {k : Nat} (j : Nat) : k + j = j + k := Nat.add_comm k j\n  exact Nat.add_zero n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `H) [(Term.implicitBinder "{" [`k] [":" `Nat] "}") (Term.explicitBinder "(" [`j] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_=_» («term_+_» `k "+" `j) "=" («term_+_» `j "+" `k)))] ":=" (Term.app `Nat.add_comm [`k `j])))) [] (Tactic.exact "exact" (Term.app `Nat.add_zero [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h4 (n : Nat) : 0 < 2 ^ n := by\n  have _ := Nat.two_pow_pos n\n  exact Nat.two_pow_pos n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h4 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_<_» (num "0") "<" («term_^_» (num "2") "^" `n)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (Term.hole "_")) [] [] ":=" (Term.app `Nat.two_pow_pos [`n])))) [] (Tactic.exact "exact" (Term.app `Nat.two_pow_pos [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h5 (n : Nat) : 0 < 2 ^ n := by\n  have _ : 0 < 2 ^ n := Nat.two_pow_pos n\n  exact Nat.two_pow_pos n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h5 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_<_» (num "0") "<" («term_^_» (num "2") "^" `n)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (Term.hole "_")) [] [(Term.typeSpec ":" («term_<_» (num "0") "<" («term_^_» (num "2") "^" `n)))] ":=" (Term.app `Nat.two_pow_pos [`n])))) [] (Tactic.exact "exact" (Term.app `Nat.two_pow_pos [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h7 (n : Nat) : n = n := by\n  let f (k : Nat) := k + 1\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h7 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticLet__ "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `f) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [] ":=" («term_+_» `k "+" (num "1"))))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h8 (n : Nat) : n = n := by\n  let f x y := x + y + n\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h8 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticLet__ "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `f) [`x `y] [] ":=" («term_+_» («term_+_» `x "+" `y) "+" `n)))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A tactic `let rec` (`Tactic.letrec`: one `letRecDecl`, its doc and attribute slots empty, an
/// empty termination suffix), and `{ tacs }` (`tacticSeqBracketed`: a whole `by`'s `tacticSeq`,
/// or one item of a sequence). Captured 2026-10-09 from one file the pin elaborated without a
/// message, in this order.
const LET_REC_TACTICS_AND_BRACKETED_SEQUENCES: &[Accepted] = &[
    Accepted {
        source: "theorem lr1 (n : Nat) : n = n := by\n  let rec go (k : Nat) : k = k := rfl\n  exact go n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `lr1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.letrec "let" "rec" (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_=_» `k "=" `k))] ":=" `rfl)) (Termination.suffix [] []))])) [] (Tactic.exact "exact" (Term.app `go [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem lr2 (n : Nat) : n = n := by\n  let rec go : ∀ k : Nat, k = k := fun _ => rfl\n  exact go n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `lr2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.letrec "let" "rec" (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [] [(Term.typeSpec ":" (Term.forall "∀" [`k] [(Term.typeSpec ":" `Nat)] "," («term_=_» `k "=" `k)))] ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))) (Termination.suffix [] []))])) [] (Tactic.exact "exact" (Term.app `go [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem lr3 (n : Nat) : n + 0 = n := by\n  let rec go (k : Nat) : k + 0 = k := by\n    simp\n  exact go n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `lr3 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.letrec "let" "rec" (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_=_» («term_+_» `k "+" (num "0")) "=" `k))] ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))))) (Termination.suffix [] []))])) [] (Tactic.exact "exact" (Term.app `go [`n]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b1 (P : Prop) (h : P) : P := by { exact h }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b1 []) (Command.declSig [(Term.explicitBinder "(" [`P] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `P] [] ")")] (Term.typeSpec ":" `P)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeqBracketed "{" [(Tactic.exact "exact" `h)] "}"))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b2 (P Q : Prop) (h : P) (q : Q) : P ∧ Q := by\n  constructor\n  { exact h }\n  { exact q }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b2 []) (Command.declSig [(Term.explicitBinder "(" [`P `Q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `P] [] ")") (Term.explicitBinder "(" [`q] [":" `Q] [] ")")] (Term.typeSpec ":" («term_∧_» `P "∧" `Q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Tactic.tacticSeqBracketed "{" [(Tactic.exact "exact" `h)] "}") [] (Tactic.tacticSeqBracketed "{" [(Tactic.exact "exact" `q)] "}")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b3 (P : Prop) (h : P) : P := by { intros; exact h }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b3 []) (Command.declSig [(Term.explicitBinder "(" [`P] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" `P] [] ")")] (Term.typeSpec ":" `P)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeqBracketed "{" [(Tactic.intros "intros" []) ";" (Tactic.exact "exact" `h)] "}"))) (Termination.suffix [] []) [])))"#,
    },
];

/// A `for` whose binder is a pattern (`for ⟨a, b⟩ in l do`, `for (a, _) in l do`: `doForDecl`'s
/// binder is a term), and a `do` block's `let rec` (`doLetRec`: `group("let" "rec")`, one
/// `letRecDecl` with empty doc and attribute slots and an empty termination suffix). Captured
/// 2026-10-09 from one file the pin elaborated without a message, in this order.
const FOR_PATTERNS_AND_DO_LET_REC: &[Accepted] = &[
    Accepted {
        source: "def fp1 (l : List (Nat × Nat)) : Nat := Id.run do\n  let mut s := 0\n  for ⟨a, b⟩ in l do\n    s := s + a + b\n  return s",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `fp1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `s) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doFor "for" [(Term.doForDecl [] (Term.anonymousCtor "⟨" [`a "," `b] "⟩") "in" `l)] "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `s) [] [] ":=" («term_+_» («term_+_» `s "+" `a) "+" `b))) [])])) []) (Term.doSeqItem (Term.doReturn "return" [`s]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def fp2 (l : List (Nat × Nat)) : Nat := Id.run do\n  let mut s := 0\n  for (a, _) in l do\n    s := s + a\n  return s",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `fp2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `s) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doFor "for" [(Term.doForDecl [] (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [(Term.hole "_")]] ")") "in" `l)] "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `s) [] [] ":=" («term_+_» `s "+" `a))) [])])) []) (Term.doSeqItem (Term.doReturn "return" [`s]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def fp3 (l : List Nat) : Nat := Id.run do\n  let mut s := 0\n  for x in l do\n    s := s + x\n  return s",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `fp3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `s) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doFor "for" [(Term.doForDecl [] `x "in" `l)] "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `s) [] [] ":=" («term_+_» `s "+" `x))) [])])) []) (Term.doSeqItem (Term.doReturn "return" [`s]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def dr1 (n : Nat) : Nat := Id.run do\n  let rec go (k : Nat) : Nat := k\n  return go n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dr1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetRec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `k)) (Termination.suffix [] []))])) []) (Term.doSeqItem (Term.doReturn "return" [(Term.app `go [`n])]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def dr2 (n : Nat) : Nat := Id.run do\n  let rec go := fun (k : Nat) => k + 1\n  return go n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dr2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Id.run [(Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetRec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [] [] ":=" (Term.fun "fun" (Term.basicFun [(Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `k ":" [`Nat] ")")] [] "=>" («term_+_» `k "+" (num "1")))))) (Termination.suffix [] []))])) []) (Term.doSeqItem (Term.doReturn "return" [(Term.app `go [`n])]) [])]))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def dr3 (n : Nat) : IO Nat := do\n  let rec loop (acc : Nat) : IO Nat := do\n    return acc\n  loop n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dr3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `IO [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetRec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `loop) [(Term.explicitBinder "(" [`acc] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `IO [`Nat]))] ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [`acc]) [])])))) (Termination.suffix [] []))])) []) (Term.doSeqItem (Term.doExpr (Term.app `loop [`n])) [])])) (Termination.suffix [] []) []) []))"#,
    },
];

/// An `induction … with` alternative whose `=>` ends its line and whose sequence starts on the next
/// line left of the pipes: `sepByIndent` positions that sequence at its first token, so it takes
/// the rest of the proof at that column (`… with | ind n ih =>⏎  cases n⏎  · rfl`). Captured
/// 2026-10-09 from one file the pin elaborated without a message, in this order.
const OWN_LINE_ALTERNATIVE_BODIES: &[Accepted] = &[
    Accepted {
        source: "theorem ia1 (n : Nat) : n + 0 = n := by\n  induction n using Nat.strongRecOn with | ind n ih =>\n  cases n\n  · rfl\n  · rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ia1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `n "+" (num "0")) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] ["using" `Nat.strongRecOn] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `ind) [`n `ih])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] []) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ia2 (n : Nat) : 0 + n = n := by\n  induction n with\n  | zero => rfl\n  | succ k ih =>\n    rw [Nat.add_succ, ih]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ia2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» (num "0") "+" `n) "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.induction "induction" [(Tactic.elimTarget [] `n)] [] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `succ) [`k `ih])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_succ) "," (Tactic.rwRule [] `ih)] "]") [])]))])])])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `obtain p := a, b` and `rcases a, b with p` (`term,+`, `elimTarget,*`: the comma stays in the
/// proof block), and a later row whose patterns share one right-hand side across an inline `|`
/// (the column rule binds only a pipe that starts its line). Captured 2026-10-09 from one file
/// the pin elaborated without a message, in this order.
const COMMA_TARGETS_AND_INLINE_SHARED_ROWS: &[Accepted] = &[
    Accepted {
        source: "theorem oc1 (a b : Nat) (ha : ∃ x, a = x) (hb : ∃ y, b = y) : True := by\n  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := ha, hb\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `oc1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`ha] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [])) "," («term_=_» `a "=" `x))] [] ")") (Term.explicitBinder "(" [`hb] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [])) "," («term_=_» `b "=" `y))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.obtain "obtain" [(Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])] "⟩")]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])] "⟩")])] [] [":=" [`ha "," `hb]]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem oc2 (a b : Nat) (ha : ∃ x, a = x) (hb : ∃ y, b = y) : True := by\n  rcases ha, hb with ⟨⟨x, h⟩, y, h'⟩\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `oc2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`ha] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [])) "," («term_=_» `a "=" `x))] [] ")") (Term.explicitBinder "(" [`hb] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] [])) "," («term_=_» `b "=" `y))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rcases "rcases" [(Tactic.elimTarget [] `ha) "," (Tactic.elimTarget [] `hb)] ["with" (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])] "⟩")]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) []) "," (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h')]) [])] "⟩")]) [])]) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def sa1 : Int → Int → Nat\n  | .ofNat _, 0 => 0\n  | .ofNat _, .ofNat (_ + 1) | .negSucc _, 0 => 0\n  | _, _ => 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sa1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Int "→" (Term.arrow `Int "→" `Nat)))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `ofNat) [(Term.hole "_")]) "," (num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `ofNat) [(Term.hole "_")]) "," (Term.app (Term.dotIdent "." `ofNat) [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.hole "_") "+" (num "1")) ")")])] "|" [(Term.app (Term.dotIdent "." `negSucc) [(Term.hole "_")]) "," (num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(Term.hole "_") "," (Term.hole "_")]] "=>" (num "1"))]) (Termination.suffix [] []) [])) []))"#,
    },
];

/// A list pattern's elements that are tuples or anonymous constructors (`(a, b) :: t`,
/// `⟨k, v⟩ :: l`, `(a, b, c) :: _`, beside another column). Captured 2026-10-09 from one file the
/// pin elaborated without a message, in this order.
const LIST_PATTERN_TUPLES: &[Accepted] = &[
    Accepted {
        source: "def cp1 : List (Nat × Nat) → Nat\n  | [] => 0\n  | (a, b) :: t => a + b + cp1 t",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `cp1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.app `List [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")]) "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_::_» (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") "::" `t)]] "=>" («term_+_» («term_+_» `a "+" `b) "+" (Term.app `cp1 [`t])))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def cp2 : List (Nat × Nat) → Nat\n  | [] => 0\n  | ⟨k, v⟩ :: l => k + v + cp2 l",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `cp2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.app `List [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")]) "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_::_» (Term.anonymousCtor "⟨" [`k "," `v] "⟩") "::" `l)]] "=>" («term_+_» («term_+_» `k "+" `v) "+" (Term.app `cp2 [`l])))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def cp3 : List (Nat × Nat × Nat) → Nat\n  | (a, b, c) :: _ => a + b + c\n  | [] => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `cp3 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.app `List [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" («term_×_» `Nat "×" `Nat)) ")")]) "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(«term_::_» (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b "," `c]] ")") "::" (Term.hole "_"))]] "=>" («term_+_» («term_+_» `a "+" `b) "+" `c)) (Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" (num "0"))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def cp4 : Nat → List (Nat × Nat) → Nat\n  | _, [] => 0\n  | a, (k, b) :: _ => a + k + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `cp4 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" (Term.arrow (Term.app `List [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")]) "→" `Nat)))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.hole "_") "," («term[_]» "[" [] "]")]] "=>" (num "0")) (Term.matchAlt "|" [[`a "," («term_::_» (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`k "," [`b]] ")") "::" (Term.hole "_"))]] "=>" («term_+_» («term_+_» `a "+" `k) "+" `b))]) (Termination.suffix [] []) [])) []))"#,
    },
];

/// A `by` inside a term whose tactics hold alternatives (`⟨by⏎  cases b with⏎  | false => rfl …,
/// trivial⟩`): the proof's pipes are the proof parser's, also beside a term `match` the plan
/// reads. Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const PROOF_PIPES_IN_TERMS: &[Accepted] = &[
    Accepted {
        source: "theorem bt1 (a : Nat) (b : Bool) : a = a ∧ True :=\n  ⟨by\n    cases b with\n    | false => rfl\n    | true => rfl, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bt1 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» `a "=" `a) "∧" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `b)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `false) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `true) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])])]))) "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem bt2 (n : Nat) : (match n with | 0 => True | _ + 1 => True) ∧ True :=\n  ⟨by\n    cases n with\n    | zero => trivial\n    | succ k => trivial, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bt2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_∧_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" `True) (Term.matchAlt "|" [[(«term_+_» (Term.hole "_") "+" (num "1"))]] "=>" `True)])) ")") "∧" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) [])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")]))]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `succ) [`k])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticTrivial "trivial")]))])])])]))) "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// Structure fields written as binders: `structImplicitBinder` (`{w : Nat}`), `structExplicitBinder`
/// (`(n : Nat)`) and `structInstBinder` (`[inst : Inhabited Nat]`), beside a simple field.
/// Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const BINDER_FIELDS: &[Accepted] = &[
    Accepted {
        source: "structure PB where\n  {w : Nat}\n  bv : Fin w",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `PB []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structImplicitBinder (Command.declModifiers [] [] [] [] [] [] []) "{" [`w] (Command.declSig [] (Term.typeSpec ":" `Nat)) "}") (Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `bv (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Fin [`w]))]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "structure PC where\n  (n : Nat)\n  [inst : Inhabited Nat]\n  m : Nat",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `PC []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structExplicitBinder (Command.declModifiers [] [] [] [] [] [] []) "(" [`n] (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [] ")") (Command.structInstBinder (Command.declModifiers [] [] [] [] [] [] []) "[" [`inst] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) "]") (Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `m (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [])])] (Command.optDeriving [])))"#,
    },
];

/// `change e at h` (`(location)?`), an anonymous tactic `let` (`let : C := v`, `letIdLhs`'s
/// `hygieneInfo`), and a term `if _ : c` (`termDepIfThenElse`, its `binderIdent` the hole).
/// Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const CHANGE_AT_ANONYMOUS_LET_AND_HOLE_CONDITIONS: &[Accepted] = &[
    Accepted {
        source: "theorem tr1 (x : Nat) (h : x + 0 = 1) : x = 1 := by\n  change x = 1 at h\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `tr1 []) (Command.declSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» («term_+_» `x "+" (num "0")) "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_=_» `x "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.change "change" («term_=_» `x "=" (num "1")) [(Tactic.location "at" (Tactic.locationHyp [`h]))]) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem tr2 : True := by\n  let : Inhabited Nat := ⟨0⟩\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `tr2 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticLet__ "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [(Term.typeSpec ":" (Term.app `Inhabited [`Nat]))] ":=" (Term.anonymousCtor "⟨" [(num "0")] "⟩")))) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def tr3 (i n : Nat) : Nat :=\n  if _ : i < n then 1 else 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tr3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`i `n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termDepIfThenElse "if" (Lean.binderIdent (Term.hole "_")) ":" («term_<_» `i "<" `n) "then" (num "1") "else" (num "0")) (Termination.suffix [] []) []) []))"#,
    },
];

/// A term `open … in t` (`Term.open`), as a declaration's value and as its type. Captured 2026-10-09
/// from one file the pin elaborated without a message, in this order.
const TERM_OPENS: &[Accepted] = &[
    Accepted {
        source: "noncomputable def to1 (p : Prop) : Bool :=\n  open scoped Classical in\n  decide p",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [(Command.noncomputable "noncomputable")] [] []) (Command.definition "def" (Command.declId `to1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" (Term.open "open" (Command.openScoped "scoped" [`Classical]) "in" (Term.app `decide [`p])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem to2 (p : Prop) :\n    open Classical in\n    decide p = decide p := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `to2 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" (Term.prop "Prop")] [] ")")] (Term.typeSpec ":" (Term.open "open" (Command.openSimple [`Classical]) "in" («term_=_» (Term.app `decide [`p]) "=" (Term.app `decide [`p]))))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
];

/// `intro` followed by match alternatives (`Tactic.introMatch`): pipes on their own lines at the
/// tactic's column, indented right of it, and inline. Captured 2026-10-09 from one file the pin
/// elaborated without a message, in this order.
const INTRO_MATCH_ALTERNATIVES: &[Accepted] = &[
    Accepted {
        source: "theorem intro_match_rows (o : Option Nat) : o = o := by\n  revert o\n  intro\n  | none => rfl\n  | some _ => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `intro_match_rows []) (Command.declSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» `o "=" `o))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.revert "revert" [`o]) [] (Tactic.introMatch "intro" (Term.matchAlts [(Term.matchAlt "|" [[`none]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[(Term.app `some [(Term.hole "_")])]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem intro_match_indented_rows (p q : Prop) (hq : q) : p ∨ q → q := by\n  intro\n    | Or.inl _ => exact hq\n    | Or.inr h => exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `intro_match_indented_rows []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" (Term.arrow («term_∨_» `p "∨" `q) "→" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.introMatch "intro" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `Or.inl [(Term.hole "_")])]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq)]))) (Term.matchAlt "|" [[(Term.app `Or.inr [`h])]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `h)])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem intro_match_inline_rows : ∀ n : Nat, n + 0 = n := by\n  intro | 0 => rfl | _ + 1 => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `intro_match_inline_rows []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [`n] [(Term.typeSpec ":" `Nat)] "," («term_=_» («term_+_» `n "+" (num "0")) "=" `n)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.introMatch "intro" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[(«term_+_» (Term.hole "_") "+" (num "1"))]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// The conv tactics that are one keyword (`whnf`, `zeta`, `simp_match`, the macros `left`, `rfl`,
/// `done`, …), `unfold`/`delta` names, `change e`, and `intro`/`ext` binders including `_` and
/// none. Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const CONV_KEYWORDS_UNFOLD_AND_INTRO: &[Accepted] = &[
    Accepted {
        source: "def convRowsF (n : Nat) : Nat := n + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `convRowsF []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» `n "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def convRowsG (n : Nat) : Nat := convRowsF n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `convRowsG []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `convRowsF [`n]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem conv_unfold_rows (n : Nat) : convRowsG n = n + 1 := by\n  conv => lhs; unfold convRowsG convRowsF",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_unfold_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `convRowsG [`n]) "=" («term_+_» `n "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.unfold "unfold" [`convRowsG `convRowsF])])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_unfold_lines_rows (n : Nat) : convRowsG n = n + 1 := by\n  conv =>\n    lhs\n    unfold convRowsG\n    unfold convRowsF",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_unfold_lines_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `convRowsG [`n]) "=" («term_+_» `n "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") [] (Tactic.Conv.unfold "unfold" [`convRowsG]) [] (Tactic.Conv.unfold "unfold" [`convRowsF])])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_delta_change_rows (n : Nat) : convRowsG n = n + 1 := by\n  conv => left; delta convRowsG; change convRowsF n\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_delta_change_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `convRowsG [`n]) "=" («term_+_» `n "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.convLeft "left") ";" (Tactic.Conv.delta "delta" [`convRowsG]) ";" (Tactic.Conv.change "change" (Term.app `convRowsF [`n]))]))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_right_rows (n : Nat) : convRowsF n = n + 1 := by\n  conv => right; rfl\n  try rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_right_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `convRowsF [`n]) "=" («term_+_» `n "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.convRight "right") ";" (Tactic.Conv.convRfl "rfl")]))) [] (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_args_rows (n : Nat) : convRowsF n = n + 1 := by\n  conv => args; whnf\n  try rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_args_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `convRowsF [`n]) "=" («term_+_» `n "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.convArgs "args") ";" (Tactic.Conv.whnf "whnf")]))) [] (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_reductions_rows (n : Nat) : convRowsF n = n + 1 := by\n  conv => lhs; zeta; reduce; cbv\n  try rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_reductions_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `convRowsF [`n]) "=" («term_+_» `n "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.zeta "zeta") ";" (Tactic.Conv.reduce "reduce") ";" (Tactic.Conv.cbv "cbv")]))) [] (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_simp_match_rows (n : Nat) : convRowsF n = n + 1 := by\n  conv => lhs; simp_match\n  try rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_simp_match_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `convRowsF [`n]) "=" («term_+_» `n "+" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.simpMatch "simp_match")]))) [] (Tactic.tacticTry_ "try" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_rfl_done_rows (n : Nat) : n = n := by\n  conv => lhs; rfl; done",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_rfl_done_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.convRfl "rfl") ";" (Tactic.Conv.convDone "done")])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_intro_ext_rows : (fun n : Nat => n + 0) = (fun n => n) := by\n  conv => lhs; intro _; rw [Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_intro_ext_rows []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`n] [(Term.typeSpec ":" `Nat)] "=>" («term_+_» `n "+" (num "0")))) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`n] [] "=>" `n)) ")")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.convIntro___ "intro" [(Lean.binderIdent (Term.hole "_"))]) ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_intro_named_rows : (fun n : Nat => n + 0) = (fun n => n) := by\n  conv => lhs; intro m; rw [Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_intro_named_rows []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`n] [(Term.typeSpec ":" `Nat)] "=>" («term_+_» `n "+" (num "0")))) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`n] [] "=>" `n)) ")")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.convIntro___ "intro" [(Lean.binderIdent `m)]) ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_ext_bare_rows : (fun n : Nat => n + 0) = (fun n => n) := by\n  conv => lhs; ext; rw [Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_ext_bare_rows []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`n] [(Term.typeSpec ":" `Nat)] "=>" («term_+_» `n "+" (num "0")))) ")") "=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.fun "fun" (Term.basicFun [`n] [] "=>" `n)) ")")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.ext "ext" []) ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_zero)] "]"))])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem conv_fun_rows (f : Nat → Nat) (h : f = id) : f 1 = 1 := by\n  conv => lhs; fun; rw [h]\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `conv_fun_rows []) (Command.declSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `f "=" `id)] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [(num "1")]) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.Conv.conv "conv" [] [] "=>" (Tactic.Conv.convSeq (Tactic.Conv.convSeq1Indented [(Tactic.Conv.lhs "lhs") ";" (Tactic.Conv.fun "fun") ";" (Tactic.Conv.convRw__ "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]"))]))) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A tactic `let rec` defined by equations (`Tactic.letrec` over a `letEqnsDecl`), with one pattern
/// and with comma-separated patterns, which stay inside the proof. Captured 2026-10-09 from one
/// file the pin elaborated without a message, in this order.
const LET_REC_EQUATIONS: &[Accepted] = &[
    Accepted {
        source: "theorem let_rec_equation_rows (m : Nat) : m + 0 = m := by\n  let rec go : ∀ n : Nat, n + 0 = n\n    | 0 => rfl\n    | n + 1 => by simp\n  exact go m",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `let_rec_equation_rows []) (Command.declSig [(Term.explicitBinder "(" [`m] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `m "+" (num "0")) "=" `m))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.letrec "let" "rec" (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letEqnsDecl (Term.letId `go) [] [(Term.typeSpec ":" (Term.forall "∀" [`n] [(Term.typeSpec ":" `Nat)] "," («term_=_» («term_+_» `n "+" (num "0")) "=" `n)))] (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" `rfl) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))))]))) (Termination.suffix [] []))])) [] (Tactic.exact "exact" (Term.app `go [`m]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem let_rec_equation_pairs_rows (l : List Nat) : l ++ [] = l := by\n  let rec go : ∀ (as : List Nat) (acc : Nat), as ++ [] = as\n    | [], acc => rfl\n    | a::as, acc => by simp\n  exact go l 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `let_rec_equation_pairs_rows []) (Command.declSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» («term_++_» `l "++" («term[_]» "[" [] "]")) "=" `l))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.letrec "let" "rec" (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letEqnsDecl (Term.letId `go) [] [(Term.typeSpec ":" (Term.forall "∀" [(Term.explicitBinder "(" [`as] [":" (Term.app `List [`Nat])] [] ")") (Term.explicitBinder "(" [`acc] [":" `Nat] [] ")")] [] "," («term_=_» («term_++_» `as "++" («term[_]» "[" [] "]")) "=" `as)))] (Term.matchAlts [(Term.matchAlt "|" [[(«term[_]» "[" [] "]") "," `acc]] "=>" `rfl) (Term.matchAlt "|" [[(«term_::_» `a "::" `as) "," `acc]] "=>" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))))]))) (Termination.suffix [] []))])) [] (Tactic.exact "exact" (Term.app `go [`l (num "0")]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem let_rec_equation_numbers_rows : True := by\n  let rec go : Nat → Nat → Nat\n    | 0, acc => acc\n    | n+1, acc => go n acc\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `let_rec_equation_numbers_rows []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.letrec "let" "rec" (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letEqnsDecl (Term.letId `go) [] [(Term.typeSpec ":" (Term.arrow `Nat "→" (Term.arrow `Nat "→" `Nat)))] (Term.matchAlts [(Term.matchAlt "|" [[(num "0") "," `acc]] "=>" `acc) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1")) "," `acc]] "=>" (Term.app `go [`n `acc]))]))) (Termination.suffix [] []))])) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `nat_lit n` (`rawNatLit`), and an anonymous term `let` (`let : T := v; e`, `let := v; e`) whose
/// `letId` is `hygieneInfo`, as a declaration's value and nested. Captured 2026-10-09 from one file
/// the pin elaborated without a message, in this order.
const RAW_NAT_LITERALS_AND_ANONYMOUS_LETS: &[Accepted] = &[
    Accepted {
        source: "def raw_nat_lit_rows : Nat := nat_lit 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `raw_nat_lit_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (rawNatLit "nat_lit" (num "0")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def raw_nat_lit_argument_rows : Nat := Nat.succ (nat_lit 3)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `raw_nat_lit_argument_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `Nat.succ [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (rawNatLit "nat_lit" (num "3")) ")")]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def anonymous_let_typed_rows (cmp : Nat → Nat → Ordering) : Ordering :=\n  let : Ord Nat := ⟨cmp⟩; compare 1 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `anonymous_let_typed_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`cmp] [":" (Term.arrow `Nat "→" (Term.arrow `Nat "→" `Ordering))] [] ")")] [(Term.typeSpec ":" `Ordering)]) (Command.declValSimple ":=" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [(Term.typeSpec ":" (Term.app `Ord [`Nat]))] ":=" (Term.anonymousCtor "⟨" [`cmp] "⟩"))) ";" (Term.app `compare [(num "1") (num "2")])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def anonymous_let_untyped_rows : Nat → Nat := fun n => let := n; 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `anonymous_let_untyped_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [] ":=" `n)) ";" (num "2")))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def anonymous_let_nested_rows : Nat → Nat := fun n => let : Nat := n; 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `anonymous_let_nested_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [(Term.typeSpec ":" `Nat)] ":=" `n)) ";" (num "2")))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def anonymous_let_value_rows : Nat := let := 1; 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `anonymous_let_value_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.let "let" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [] ":=" (num "1"))) ";" (num "2")) (Termination.suffix [] []) []) []))"#,
    },
];

/// `where` declarations led by an attribute line (`@[specialize]⏎go …`), the first and a later one;
/// a structure field that overrides an inherited default with no type (`x := 2`); and `where
/// finally` (`Term.whereFinally`), alone and after a declaration at its column (`allowTrailingSep`).
/// Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const WHERE_ATTRIBUTES_DEFAULT_OVERRIDES_AND_FINALLY: &[Accepted] = &[
    Accepted {
        source: "def where_attribute_line_rows (l : List Nat) : Nat := go l 0\n  where\n  @[specialize]\n  go : List Nat → Nat → Nat\n    | [], acc => acc\n    | a::as, acc => go as (a + acc)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `where_attribute_line_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`Nat])] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `go [`l (num "0")]) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.specialize "specialize" []))] "]")] (Term.letDecl (Term.letEqnsDecl (Term.letId `go) [] [(Term.typeSpec ":" (Term.arrow (Term.app `List [`Nat]) "→" (Term.arrow `Nat "→" `Nat)))] (Term.matchAlts [(Term.matchAlt "|" [[(«term[_]» "[" [] "]") "," `acc]] "=>" `acc) (Term.matchAlt "|" [[(«term_::_» `a "::" `as) "," `acc]] "=>" (Term.app `go [`as (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `a "+" `acc) ")")]))]))) (Termination.suffix [] []))] [])]) []))"#,
    },
    Accepted {
        source: "def where_attribute_lines_rows (n : Nat) : Nat := go n + aux n\n  where\n  @[inline]\n  go (i : Nat) : Nat := i + 1\n  @[specialize]\n  aux (i : Nat) : Nat := i",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `where_attribute_lines_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (Term.app `go [`n]) "+" (Term.app `aux [`n])) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `inline []))] "]")] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" («term_+_» `i "+" (num "1")))) (Termination.suffix [] [])) [] (Term.letRecDecl [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.specialize "specialize" []))] "]")] (Term.letDecl (Term.letIdDecl (Term.letId `aux) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `i)) (Termination.suffix [] []))] [])]) []))"#,
    },
    Accepted {
        source: "structure DefaultOverrideRowsBase where\n  x : Nat := 1\n  y : Bool := true",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `DefaultOverrideRowsBase []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [(Term.binderDefault ":=" (num "1"))]) (Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `y (Command.optDeclSig [] [(Term.typeSpec ":" `Bool)]) [(Term.binderDefault ":=" `true)])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "structure DefaultOverrideRows extends DefaultOverrideRowsBase where\n  x := 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `DefaultOverrideRows []) (Command.optDeclSig [] []) [(Command.extends "extends" [(Command.structParent [] `DefaultOverrideRowsBase)] [])] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `x (Command.optDeclSig [] []) [(Term.binderDefault ":=" (num "2"))])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "structure DefaultOverrideTypedRows extends DefaultOverrideRowsBase where\n  y := false\n  z : Nat := 3",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `DefaultOverrideTypedRows []) (Command.optDeclSig [] []) [(Command.extends "extends" [(Command.structParent [] `DefaultOverrideRowsBase)] [])] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `y (Command.optDeclSig [] []) [(Term.binderDefault ":=" `false)]) (Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `z (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) [(Term.binderDefault ":=" (num "3"))])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "def where_finally_rows (n : Nat) : Fin (n + 1) :=\n  ⟨0, ?_⟩\n  where finally\n  exact Nat.zero_lt_succ n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `where_finally_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Fin [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `n "+" (num "1")) ")")]))]) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0") "," (Term.syntheticHole "?" "_")] "⟩") (Termination.suffix [] []) [(Term.whereDecls "where" [] [(Term.whereFinally "finally" [(Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.app `Nat.zero_lt_succ [`n]))]))] [])])]) []))"#,
    },
    Accepted {
        source: "def where_finally_sequence_rows (n : Nat) : Fin (n + 1) :=\n  ⟨0, ?_⟩\n  where finally\n  have h : 0 < n + 1 := Nat.zero_lt_succ n\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `where_finally_sequence_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Fin [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `n "+" (num "1")) ")")]))]) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0") "," (Term.syntheticHole "?" "_")] "⟩") (Termination.suffix [] []) [(Term.whereDecls "where" [] [(Term.whereFinally "finally" [(Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" («term_<_» (num "0") "<" («term_+_» `n "+" (num "1"))))] ":=" (Term.app `Nat.zero_lt_succ [`n])))) [] (Tactic.exact "exact" `h)]))] [])])]) []))"#,
    },
    Accepted {
        source: "def where_declarations_finally_rows (n : Nat) : Fin (n + 1) × Nat :=\n  (⟨0, ?_⟩, go n)\n  where\n  go (k : Nat) : Nat := k\n  finally\n  exact Nat.zero_lt_succ n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `where_declarations_finally_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_×_» (Term.app `Fin [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `n "+" (num "1")) ")")]) "×" `Nat))]) (Command.declValSimple ":=" (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(Term.anonymousCtor "⟨" [(num "0") "," (Term.syntheticHole "?" "_")] "⟩") "," [(Term.app `go [`n])]] ")") (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `k)) (Termination.suffix [] [])) []] [(Term.whereFinally "finally" [(Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.app `Nat.zero_lt_succ [`n]))]))] [])])]) []))"#,
    },
];

/// `@[method_specs_simp]` (`Attr.method_specs_simp`, `simp`'s grammar): bare, reversed, and with a
/// phase and a priority. Captured 2026-10-09 from one file the pin elaborated without a message, in
/// this order.
const METHOD_SPECS_SIMP_ATTRIBUTES: &[Accepted] = &[
    Accepted {
        source: "@[method_specs_simp] theorem method_specs_simp_rows (a b : Nat) : Add.add a b = a + b := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.method_specs_simp "method_specs_simp" [] [] []))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `method_specs_simp_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `Add.add [`a `b]) "=" («term_+_» `a "+" `b)))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[method_specs_simp ←] theorem method_specs_simp_reverse_rows (a b : Nat) : a + b = Add.add a b := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.method_specs_simp "method_specs_simp" [] ["←"] []))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `method_specs_simp_reverse_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `b) "=" (Term.app `Add.add [`a `b])))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[method_specs_simp ↓ 100] theorem method_specs_simp_phase_rows (a b : Nat) : Mul.mul a b = a * b := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.method_specs_simp "method_specs_simp" [(Tactic.simpPre "↓")] [] [(num "100")]))] "]")] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `method_specs_simp_phase_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `Mul.mul [`a `b]) "=" («term_*_» `a "*" `b)))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
];

/// `simp` rules that hold their own commas: a nested rule list, an anonymous constructor, and a
/// `show ∀ a, p` whose binder comma is its own; and `show ∀ a, p by tac`, whose `by` closes the
/// annotation past the binder body. Captured 2026-10-09 from one file the pin elaborated without a
/// message, in this order.
const SIMP_RULE_COMMAS_AND_SHOW_BINDERS: &[Accepted] = &[
    Accepted {
        source: "theorem simp_show_forall_by_rows (m : Nat) : (m + 1) + 1 = m + 2 := by\n  simp [show ∀ a, a + 1 + 1 = a + 2 by omega]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `simp_show_forall_by_rows []) (Command.declSig [(Term.explicitBinder "(" [`m] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `m "+" (num "1")) ")") "+" (num "1")) "=" («term_+_» `m "+" (num "2"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] (Term.show "show" (Term.forall "∀" [`a] [] "," («term_=_» («term_+_» («term_+_» `a "+" (num "1")) "+" (num "1")) "=" («term_+_» `a "+" (num "2")))) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem simp_show_nested_list_rows (x : Nat) (hx : x = 1) : x + 0 = 1 := by\n  simp only [show x + 0 = 1 by simp only [Nat.add_zero, hx]]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `simp_show_nested_list_rows []) (Command.declSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")") (Term.explicitBinder "(" [`hx] [":" («term_=_» `x "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `x "+" (num "0")) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] (Term.show "show" («term_=_» («term_+_» `x "+" (num "0")) "=" (num "1")) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] `Nat.add_zero) "," (Tactic.simpLemma [] [] `hx)] "]"] [])])))))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem simp_show_forall_from_rows (m : Nat) : m + 0 = m := by\n  simp only [show ∀ a : Nat, a + 0 = a from fun a => Nat.add_zero a]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `simp_show_forall_from_rows []) (Command.declSig [(Term.explicitBinder "(" [`m] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `m "+" (num "0")) "=" `m))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] (Term.show "show" (Term.forall "∀" [`a] [(Term.typeSpec ":" `Nat)] "," («term_=_» («term_+_» `a "+" (num "0")) "=" `a)) (Term.fromTerm "from" (Term.fun "fun" (Term.basicFun [`a] [] "=>" (Term.app `Nat.add_zero [`a]))))))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem simp_anonymous_constructor_rows (p : Nat × Nat) (h : p = ⟨1, 2⟩) : p.1 = 1 := by\n  simp [h, show (⟨1, 2⟩ : Nat × Nat).1 = 1 from rfl]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `simp_anonymous_constructor_rows []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `p "=" (Term.anonymousCtor "⟨" [(num "1") "," (num "2")] "⟩"))] [] ")")] (Term.typeSpec ":" («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] (Term.show "show" («term_=_» (Term.proj (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.anonymousCtor "⟨" [(num "1") "," (num "2")] "⟩") ":" [(«term_×_» `Nat "×" `Nat)] ")") "." (fieldIdx "1")) "=" (num "1")) (Term.fromTerm "from" `rfl)))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem show_forall_by_rows : ∀ a : Nat, a = a := by\n  exact show ∀ a : Nat, a = a by intro a; rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `show_forall_by_rows []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [`a] [(Term.typeSpec ":" `Nat)] "," («term_=_» `a "=" `a)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.show "show" (Term.forall "∀" [`a] [(Term.typeSpec ":" `Nat)] "," («term_=_» `a "=" `a)) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intro "intro" [`a]) ";" (Tactic.tacticRfl "rfl")])))))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Constructors (`ctor := docComment? "| " declModifiers rawIdent optDeclSig`) named by a keyword
/// (`| return`), `protected`, and with their doc comment after the `|` (in `declModifiers`).
/// Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const CONSTRUCTOR_NAMES_AND_MODIFIERS: &[Accepted] = &[
    Accepted {
        source: "inductive KeywordCtorRows (σ : Type) where\n  /-- pure -/\n  | pure : σ → KeywordCtorRows σ\n  /-- return -/\n  | return : σ → KeywordCtorRows σ\n  | break    : σ → KeywordCtorRows σ",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `KeywordCtorRows []) (Command.optDeclSig [(Term.explicitBinder "(" [`σ] [":" (Term.type "Type" [])] [] ")")] []) ["where"] [(Command.ctor [(Command.docComment "/--" "pure -/")] "|" (Command.declModifiers [] [] [] [] [] [] []) `pure (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `σ "→" (Term.app `KeywordCtorRows [`σ])))])) (Command.ctor [(Command.docComment "/--" "return -/")] "|" (Command.declModifiers [] [] [] [] [] [] []) `return (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `σ "→" (Term.app `KeywordCtorRows [`σ])))])) (Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `break (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `σ "→" (Term.app `KeywordCtorRows [`σ])))]))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "inductive ProtectedCtorRows (r : Nat → Nat → Prop) : Nat → Nat → Prop where\n  | protected inl {a c} : r a c → ProtectedCtorRows r a c",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `ProtectedCtorRows []) (Command.optDeclSig [(Term.explicitBinder "(" [`r] [":" (Term.arrow `Nat "→" (Term.arrow `Nat "→" (Term.prop "Prop")))] [] ")")] [(Term.typeSpec ":" (Term.arrow `Nat "→" (Term.arrow `Nat "→" (Term.prop "Prop"))))]) ["where"] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [(Command.protected "protected")] [] [] []) `inl (Command.optDeclSig [(Term.implicitBinder "{" [`a `c] [] "}")] [(Term.typeSpec ":" (Term.arrow (Term.app `r [`a `c]) "→" (Term.app `ProtectedCtorRows [`r `a `c])))]))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "inductive InnerDocCtorRows : Type where\n  | /-- The first. -/\n    first\n  | /-- The second. -/\n    second (n : Nat)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `InnerDocCtorRows []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.type "Type" []))]) ["where"] [(Command.ctor [] "|" (Command.declModifiers [(Command.docComment "/--" "The first. -/")] [] [] [] [] [] []) `first (Command.optDeclSig [] [])) (Command.ctor [] "|" (Command.declModifiers [(Command.docComment "/--" "The second. -/")] [] [] [] [] [] []) `second (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] []))] [] (Command.optDeriving [])))"#,
    },
];

/// A tactic `match`/`cases` alternative whose right-hand side is a hole (`matchRhs := hole <|>
/// syntheticHole <|> tacticSeq`), on its own line and inline; and a `by` block ended by the `,` of
/// its anonymous constructor at the tactics' column (`allowTrailingSep`). Captured 2026-10-09 from
/// one file the pin elaborated without a message, in this order.
const HOLE_ALTERNATIVES_AND_CONSTRUCTOR_PROOFS: &[Accepted] = &[
    Accepted {
        source: "theorem match_hole_alternative_rows (n : Nat) : n = n := by\n  match n with\n  | 0 => ?_\n  | k + 1 => rfl\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `match_hole_alternative_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.syntheticHole "?" "_")) (Term.matchAlt "|" [[(«term_+_» `k "+" (num "1"))]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem cases_hole_alternative_rows (n : Nat) : n = n := by\n  cases n with\n  | zero => ?_\n  | succ k => rfl\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `cases_hole_alternative_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.cases "cases" [(Tactic.elimTarget [] `n)] [] [(Tactic.inductionAlts "with" [] [(Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `zero) [])] ["=>" (Term.syntheticHole "?" "_")]) (Tactic.inductionAlt [(Tactic.inductionAltLHS "|" (group [] `succ) [`k])] ["=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))])])]) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem inline_hole_alternative_rows (n : Nat) : n = n := by\n  match n with | 0 => ?_ | k + 1 => rfl\n  rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `inline_hole_alternative_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.syntheticHole "?" "_")) (Term.matchAlt "|" [[(«term_+_» `k "+" (num "1"))]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])) [] (Tactic.tacticRfl "rfl")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem anonymous_constructor_proofs_rows (p q : Prop) (hp : p) (hq : q) : p ∧ q :=\n  ⟨by\n    exact hp\n    , by exact hq⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `anonymous_constructor_proofs_rows []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp) []]))) "," (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq)])))] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// `grind` with `only` and its parameter list (`grindParam := grindErase <|> grindLemmaMin <|>
/// grindLemma <|> anchor`): lemmas, `only`, modifiers (`=`, `←`, `→`, `cases`), and an erasure.
/// Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const GRIND_PARAMETERS: &[Accepted] = &[
    Accepted {
        source: "theorem grind_lemma_rows (a b : Nat) (h : a = b) : b = a := by\n  grind [Nat.add_comm]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `grind_lemma_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig []) [] ["[" [(Tactic.grindParam (Tactic.grindLemma [] `Nat.add_comm))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem grind_lemmas_rows (a b : Nat) (h : a = b) : b = a := by\n  grind [Nat.add_comm, Nat.mul_comm]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `grind_lemmas_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig []) [] ["[" [(Tactic.grindParam (Tactic.grindLemma [] `Nat.add_comm)) "," (Tactic.grindParam (Tactic.grindLemma [] `Nat.mul_comm))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem grind_only_rows (a b : Nat) (h : a = b) : b = a := by\n  grind only [Nat.add_comm]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `grind_only_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig []) ["only"] ["[" [(Tactic.grindParam (Tactic.grindLemma [] `Nat.add_comm))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem grind_modifier_rows (a b : Nat) (h : a = b) : b = a := by\n  grind [= Nat.add_comm, ← Nat.mul_comm, → Nat.le_of_lt]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `grind_modifier_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig []) [] ["[" [(Tactic.grindParam (Tactic.grindLemma [(Attr.grindMod (Attr.grindEq "=" []))] `Nat.add_comm)) "," (Tactic.grindParam (Tactic.grindLemma [(Attr.grindMod (Attr.grindBwd (patternIgnore (token.«←» "←")) []))] `Nat.mul_comm)) "," (Tactic.grindParam (Tactic.grindLemma [(Attr.grindMod (Attr.grindFwd (patternIgnore (token.«→» "→"))))] `Nat.le_of_lt))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem grind_cases_rows (b : Bool) : b = true ∨ b = false := by\n  grind [cases Bool]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `grind_cases_rows []) (Command.declSig [(Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] (Term.typeSpec ":" («term_∨_» («term_=_» `b "=" `true) "∨" («term_=_» `b "=" `false)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig []) [] ["[" [(Tactic.grindParam (Tactic.grindLemma [(Attr.grindMod (Attr.grindCases "cases"))] `Bool))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem grind_erase_rows (a b : Nat) (h : a = b) : b = a := by\n  grind [-List.length_cons]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `grind_erase_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.grind "grind" (Tactic.optConfig []) [] ["[" [(Tactic.grindParam (Tactic.grindErase "-" `List.length_cons))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Inside a syntax quotation, an application headed by an antiquotation (`$f $a`, `$f ($a)`), as a
/// value and as an equation's pattern (the `app_unexpander` shape). Captured 2026-10-09 from one
/// file the pin elaborated without a message, in this order.
const ANTIQUOTATION_HEADS: &[Accepted] = &[
    Accepted {
        source: "def antiquotation_head_rows (f a : Lean.Term) : Lean.MacroM Lean.Term := `($f $a)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `antiquotation_head_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`f `a] [":" `Lean.Term] [] ")")] [(Term.typeSpec ":" (Term.app `Lean.MacroM [`Lean.Term]))]) (Command.declValSimple ":=" (Term.quot "`(" (Term.app (term.pseudo.antiquot "$" [] `f []) [(term.pseudo.antiquot "$" [] `a [])]) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def antiquotation_head_paren_rows (f a : Lean.Term) : Lean.MacroM Lean.Term := `($f ($a))",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `antiquotation_head_paren_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`f `a] [":" `Lean.Term] [] ")")] [(Term.typeSpec ":" (Term.app `Lean.MacroM [`Lean.Term]))]) (Command.declValSimple ":=" (Term.quot "`(" (Term.app (term.pseudo.antiquot "$" [] `f []) [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (term.pseudo.antiquot "$" [] `a []) ")")]) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def antiquotation_head_pattern_rows : Lean.Syntax → Lean.MacroM Lean.Syntax\n  | `($f $a) => `($f $a)\n  | s => pure s",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `antiquotation_head_pattern_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Lean.Syntax "→" (Term.app `Lean.MacroM [`Lean.Syntax])))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.quot "`(" (Term.app (term.pseudo.antiquot "$" [] `f []) [(term.pseudo.antiquot "$" [] `a [])]) ")")]] "=>" (Term.quot "`(" (Term.app (term.pseudo.antiquot "$" [] `f []) [(term.pseudo.antiquot "$" [] `a [])]) ")")) (Term.matchAlt "|" [[`s]] "=>" (Term.app `pure [`s]))]) (Termination.suffix [] []) [])) []))"#,
    },
];

/// `if`/`bif` inside a term quotation, plain, with an antiquotation condition and nested: the match
/// planner leaves a quotation to its own term. Captured 2026-10-09 from one file the pin
/// elaborated without a message, in this order.
const QUOTATION_CONDITIONALS: &[Accepted] = &[
    Accepted {
        source: "def quotation_if_rows : Lean.MacroM Lean.Term := `(if c then 1 else 2)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `quotation_if_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Lean.MacroM [`Lean.Term]))]) (Command.declValSimple ":=" (Term.quot "`(" (termIfThenElse "if" `c "then" (num "1") "else" (num "2")) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def quotation_if_antiquotation_rows (c : Lean.Term) : Lean.MacroM Lean.Term := `(if $c then 1 else 2)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `quotation_if_antiquotation_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Lean.Term] [] ")")] [(Term.typeSpec ":" (Term.app `Lean.MacroM [`Lean.Term]))]) (Command.declValSimple ":=" (Term.quot "`(" (termIfThenElse "if" (term.pseudo.antiquot "$" [] `c []) "then" (num "1") "else" (num "2")) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def quotation_nested_if_rows (c : Lean.Term) : Lean.MacroM Lean.Term := `(f (if $c then 1 else 2))",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `quotation_nested_if_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Lean.Term] [] ")")] [(Term.typeSpec ":" (Term.app `Lean.MacroM [`Lean.Term]))]) (Command.declValSimple ":=" (Term.quot "`(" (Term.app `f [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (termIfThenElse "if" (term.pseudo.antiquot "$" [] `c []) "then" (num "1") "else" (num "2")) ")")]) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def quotation_bif_rows (c : Lean.Term) : Lean.MacroM Lean.Term := `(bif $c then 1 else 2)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `quotation_bif_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Lean.Term] [] ")")] [(Term.typeSpec ":" (Term.app `Lean.MacroM [`Lean.Term]))]) (Command.declValSimple ":=" (Term.quot "`(" (boolIfThenElse "bif" (term.pseudo.antiquot "$" [] `c []) "then" (num "1") "else" (num "2")) ")") (Termination.suffix [] []) []) []))"#,
    },
];

/// A `where` field defined by equations after the names it binds (`f x | p => e`), and an
/// alternative whose body holds a binder's comma and type (`| p => ∃ h : t, q`), on one line and
/// across lines. Captured 2026-10-09 from one file the pin elaborated without a message, in this
/// order.
const FIELD_EQUATIONS_AND_BINDER_BODIES: &[Accepted] = &[
    Accepted {
        source: "structure FieldEquationRows where\n  f : Nat → Option Nat → Prop",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `FieldEquationRows []) (Command.optDeclSig [] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `f (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" (Term.arrow (Term.app `Option [`Nat]) "→" (Term.prop "Prop"))))]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "def field_equation_binder_rows : FieldEquationRows where\n  f x\n    | .some y => x = y\n    | .none => False",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `field_equation_binder_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" `FieldEquationRows)]) (Command.whereStructInst "where" (Term.structInstFields [(Term.structInstField (Term.structInstLVal `f []) [[`x] [] (Term.structInstFieldEqns [] (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `some) [`y])]] "=>" («term_=_» `x "=" `y)) (Term.matchAlt "|" [[(Term.dotIdent "." `none)]] "=>" `False)]))])]) []) []))"#,
    },
    Accepted {
        source: "def field_equation_exists_rows : FieldEquationRows where\n  f x\n    | .some y =>\n      ∃ h : x = y,\n        x = x ∧\n        h = h\n    | .none => False",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `field_equation_exists_rows []) (Command.optDeclSig [] [(Term.typeSpec ":" `FieldEquationRows)]) (Command.whereStructInst "where" (Term.structInstFields [(Term.structInstField (Term.structInstLVal `f []) [[`x] [] (Term.structInstFieldEqns [] (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `some) [`y])]] "=>" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" («term_=_» `x "=" `y)])) "," («term_∧_» («term_=_» `x "=" `x) "∧" («term_=_» `h "=" `h)))) (Term.matchAlt "|" [[(Term.dotIdent "." `none)]] "=>" `False)]))])]) []) []))"#,
    },
    Accepted {
        source: "def exists_alternative_rows (x : Nat) : Option Nat → Prop\n  | .some y => ∃ z, x = z ∧ z = y\n  | .none => False",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `exists_alternative_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.arrow (Term.app `Option [`Nat]) "→" (Term.prop "Prop")))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `some) [`y])]] "=>" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `z)] [])) "," («term_∧_» («term_=_» `x "=" `z) "∧" («term_=_» `z "=" `y)))) (Term.matchAlt "|" [[(Term.dotIdent "." `none)]] "=>" `False)]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def exists_typed_alternative_rows (x : Nat) : Option Nat → Prop\n  | .some y =>\n    ∃ h : x = y,\n      h = h\n  | .none => False",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `exists_typed_alternative_rows []) (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.arrow (Term.app `Option [`Nat]) "→" (Term.prop "Prop")))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `some) [`y])]] "=>" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" («term_=_» `x "=" `y)])) "," («term_=_» `h "=" `h))) (Term.matchAlt "|" [[(Term.dotIdent "." `none)]] "=>" `False)]) (Termination.suffix [] []) [])) []))"#,
    },
];

/// A projection whose field is a keyword spelled as an identifier (`(a).then b`, `rawIdent`), after a
/// parenthesis and chained. Captured 2026-10-09 from one file the pin elaborated without a message,
/// in this order.
const KEYWORD_FIELD_PROJECTIONS: &[Accepted] = &[
    Accepted {
        source: "def dtA (a b : Ordering) : Ordering := (a).then b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dtA []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Ordering] [] ")")] [(Term.typeSpec ":" `Ordering)]) (Command.declValSimple ":=" (Term.app (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `a ")") "." `then) [`b]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem dtB : ∀ (o₁ o₂ o₃ : Ordering), (o₁.then o₂).then o₃ = o₁.then (o₂.then o₃) := by decide",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `dtB []) (Command.declSig [] (Term.typeSpec ":" (Term.forall "∀" [(Term.explicitBinder "(" [`o₁ `o₂ `o₃] [":" `Ordering] [] ")")] [] "," («term_=_» (Term.app (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `o₁.then [`o₂]) ")") "." `then) [`o₃]) "=" (Term.app `o₁.then [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `o₂.then [`o₃]) ")")]))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A tactic `if`'s branch holding a `<;>` chain, alone and after another tactic: the `<;>` is the
/// branch's, not a chain around the `if`. Captured 2026-10-09 from one file the pin elaborated
/// without a message, in this order.
const TACTIC_IF_BRANCH_CHAINS: &[Accepted] = &[
    Accepted {
        source: "theorem tactic_if_branch_chain_rows (a b : Nat) : a + 0 = a := by\n  if hb : b = 0 then\n    simp <;> simp\n  else\n    simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `tactic_if_branch_chain_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacDepIfThenElse "if" (Lean.binderIdent `hb) ":" («term_=_» `b "=" (num "0")) "then" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))])) "else" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem tactic_if_branch_sequence_chain_rows (a b : Nat) : a + 0 = a := by\n  if hb : b = 0 then\n    subst hb\n    simp <;> simp\n  else\n    simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `tactic_if_branch_sequence_chain_rows []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" `a))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacDepIfThenElse "if" (Lean.binderIdent `hb) ":" («term_=_» `b "=" (num "0")) "then" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.subst "subst" [`hb]) [] (Tactic.«tactic_<;>_» (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))])) "else" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `simp`'s discharger slot (`(discharger := tacs)`, `(disch := tacs)`), before `only` and the
/// rules. Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const SIMP_DISCHARGERS: &[Accepted] = &[
    Accepted {
        source: "theorem simp_discharger_rows (a : Nat) (h : a = 0) : a + 0 = 0 := by\n  simp (discharger := assumption) [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `simp_discharger_rows []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [(Tactic.discharger "(" (patternIgnore (token.discharger "discharger")) ":=" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.assumption "assumption")])) ")")] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem simp_disch_rows (a : Nat) (h : a = 0) : a + 0 = 0 := by\n  simp (disch := assumption) only [h, Nat.add_zero]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `simp_disch_rows []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» («term_+_» `a "+" (num "0")) "=" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [(Tactic.discharger "(" (patternIgnore (token.disch "disch")) ":=" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.assumption "assumption")])) ")")] ["only"] ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `Nat.add_zero)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A tactic `match` alternative whose pattern groups share one body (`| 0 | 1 => rfl`, one
/// `matchAlt` with its groups separated by their `|`s), on separate lines, inline, and with a hole
/// body. Captured 2026-10-09 from one file the pin elaborated without a message, in this order.
const SHARED_MATCH_ALTERNATIVES: &[Accepted] = &[
    Accepted {
        source: "theorem shared_match_alternative_rows (n : Nat) : n = n := by\n  match n with\n  | 0 | 1 => rfl\n  | _ + 2 => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `shared_match_alternative_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")] "|" [(num "1")]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) (Term.matchAlt "|" [[(«term_+_» (Term.hole "_") "+" (num "2"))]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem shared_inline_match_alternative_rows (n : Nat) : n = n := by\n  match n with | 0 | 1 | _ + 2 => rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `shared_inline_match_alternative_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")] "|" [(num "1")] "|" [(«term_+_» (Term.hole "_") "+" (num "2"))]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem shared_match_hole_alternative_rows (n : Nat) : n = n := by\n  match n with\n  | 0 | 1 => ?_\n  | _ + 2 => rfl\n  all_goals rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `shared_match_hole_alternative_rows []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")] "|" [(num "1")]] "=>" (Term.syntheticHole "?" "_")) (Term.matchAlt "|" [[(«term_+_» (Term.hole "_") "+" (num "2"))]] "=>" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))])) [] (Tactic.allGoals "all_goals" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `a ≈ b` (`infix:50 " ≈ " => HasEquiv.Equiv`, `term_≈_`).
const EQUIVALENCES: &[Accepted] = &[Accepted {
    source: "theorem eq1 {α : Type} [HasEquiv α] (a b : α) (h : a ≈ b) : a ≈ b := h",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `eq1 []) (Command.declSig [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [])] "}") (Term.instBinder "[" [] (Term.app `HasEquiv [`α]) "]") (Term.explicitBinder "(" [`a `b] [":" `α] [] ")") (Term.explicitBinder "(" [`h] [":" («term_≈_» `a "≈" `b)] [] ")")] (Term.typeSpec ":" («term_≈_» `a "≈" `b))) (Command.declValSimple ":=" `h (Termination.suffix [] []) [])))"#,
}];

/// Named patterns as constructor arguments (`.inner l@(.inner ..) _`, `r@.leaf`, `some p@⟨a, _⟩`):
/// `namedPattern := ident noWs "@" noWs (ident ":")? term:max`, so the name, the touching `@` and the
/// atomic pattern touching it are one argument.
const NAMED_PATTERN_ARGUMENTS: &[Accepted] = &[
    Accepted {
        source: "inductive T where\n  | leaf\n  | inner (l : T) (r : T)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `T []) (Command.optDeclSig [] []) ["where"] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `leaf (Command.optDeclSig [] [])) (Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `inner (Command.optDeclSig [(Term.explicitBinder "(" [`l] [":" `T] [] ")") (Term.explicitBinder "(" [`r] [":" `T] [] ")")] []))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "def np1 : T → Nat\n  | .inner l@(.inner ..) _ => 1\n  | _ => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `np1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `T "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `inner) [(Term.namedPattern `l "@" [] (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app (Term.dotIdent "." `inner) [(Term.ellipsis "..")]) ")")) (Term.hole "_")])]] "=>" (num "1")) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" (num "0"))]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def np2 : T → T\n  | .inner l@(.inner _ _) r@.leaf => .inner r l\n  | t => t",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `np2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `T "→" `T))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `inner) [(Term.namedPattern `l "@" [] (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app (Term.dotIdent "." `inner) [(Term.hole "_") (Term.hole "_")]) ")")) (Term.namedPattern `r "@" [] (Term.dotIdent "." `leaf))])]] "=>" (Term.app (Term.dotIdent "." `inner) [`r `l])) (Term.matchAlt "|" [[`t]] "=>" `t)]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def np3 : Option (Nat × Nat) → Nat\n  | some p@⟨a, _⟩ => a + p.2\n  | none => 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `np3 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")]) "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [(Term.namedPattern `p "@" [] (Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩"))])]] "=>" («term_+_» `a "+" (Term.proj `p "." (fieldIdx "2")))) (Term.matchAlt "|" [[`none]] "=>" (num "0"))]) (Termination.suffix [] []) [])) []))"#,
    },
];

/// An `if` or `match` right after a `←` is a do element (`leftArrow doElemParser` in `doIdDecl`,
/// `doPatDecl` and `nestedAction`): `Term.doIf` / `Term.doMatch` with do-sequence branches, never
/// `doExpr` of a term `if`, whose nested actions would be lifted out of their branch. `bif` stays a
/// term.
const ARROW_DO_ELEMENTS: &[Accepted] = &[
    Accepted {
        source: "def ae1 (c : Bool) : Id Nat := do\n  let x ← if c then pure 1 else pure 2\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Bool] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" [] (Term.letConfig []) (Term.doIdDecl `x [] "←" (Term.doIf "if" (Term.doIfProp [] `c) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "1")])) [])]) [] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "2")])) [])])]))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ae2 (c : Bool) : Id Nat := do\n  let x ←\n    if c then pure 1\n    else pure 2\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Bool] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" [] (Term.letConfig []) (Term.doIdDecl `x [] "←" (Term.doIf "if" (Term.doIfProp [] `c) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "1")])) [])]) [] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "2")])) [])])]))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ae3 (o : Option Nat) : Id Nat := do\n  let x ← match o with\n    | some n => pure n\n    | none => pure 0\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" [] (Term.letConfig []) (Term.doIdDecl `x [] "←" (Term.doMatch "match" [] [] [] [(Term.matchDiscr [] `o)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [`n])]] "=>" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [`n])) [])])) (Term.matchAlt "|" [[`none]] "=>" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "0")])) [])]))])))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ae4 (c : Bool) : Id Nat := do\n  let x := (← if c then pure 1 else pure 2)\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Bool] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" [] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [] ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.nestedAction "←" (Term.doIf "if" (Term.doIfProp [] `c) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "1")])) [])]) [] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "2")])) [])])])) ")")))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ae5 (c : Bool) : Id Nat := do\n  let mut y := 0\n  y ← if c then pure 1 else pure 2\n  return y",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Bool] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `y) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doReassignArrow (Term.doIdDecl `y [] "←" (Term.doIf "if" (Term.doIfProp [] `c) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "1")])) [])]) [] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "2")])) [])])]))) []) (Term.doSeqItem (Term.doReturn "return" [`y]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ae6 (p : Option (Nat × Nat)) : Id Nat := do\n  let (a, b) ← match p with\n    | some q => pure q\n    | none => pure (0, 0)\n  return a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae6 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" (Term.app `Option [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")])] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" [] (Term.letConfig []) (Term.doPatDecl (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") [] "←" (Term.doMatch "match" [] [] [] [(Term.matchDiscr [] `p)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.app `some [`q])]] "=>" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [`q])) [])])) (Term.matchAlt "|" [[`none]] "=>" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(num "0") "," [(num "0")]] ")")])) [])]))])) [])) []) (Term.doSeqItem (Term.doReturn "return" [(«term_+_» `a "+" `b)]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ae7 (c : Bool) : Id Nat := do\n  let x ← bif c then pure 1 else pure 2\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae7 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Bool] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" [] (Term.letConfig []) (Term.doIdDecl `x [] "←" (Term.doExpr (boolIfThenElse "bif" `c "then" (Term.app `pure [(num "1")]) "else" (Term.app `pure [(num "2")]))))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def ae8 (c d : Bool) : Id Nat := do\n  let x ← if c then\n      pure 1\n    else if d then\n      pure 2\n    else\n      pure 3\n  return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `ae8 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c `d] [":" `Bool] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" [] (Term.letConfig []) (Term.doIdDecl `x [] "←" (Term.doIf "if" (Term.doIfProp [] `c) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "1")])) [])]) [(group (group "else" "if") (Term.doIfProp [] `d) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "2")])) [])]))] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "3")])) [])])]))) []) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
];

/// `injection h with _ h₂`: the names are `ident <|> hole`, so a `_` is a `Term.hole`.
const INJECTION_HOLES: &[Accepted] = &[
    Accepted {
        source: "theorem inj1 (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by\n  injection h with h'\n  exact h'",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `inj1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» (Term.app `Nat.succ [`a]) "=" (Term.app `Nat.succ [`b]))] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.injection "injection" `h ["with" [`h']]) [] (Tactic.exact "exact" `h')]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem inj2 (a b c d : Nat) (h : (a, b) = (c, d)) : b = d := by\n  injection h with _ h₂\n  exact h₂",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `inj2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c `d] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") "=" (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`c "," [`d]] ")"))] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" `d))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.injection "injection" `h ["with" [(Term.hole "_") `h₂]]) [] (Tactic.exact "exact" `h₂)]))) (Termination.suffix [] []) [])))"#,
    },
];

/// The ranges with an unbounded side (`Init/Data/Range/Polymorphic/PRange.lean`, namespace `Std`):
/// `*...b`, `*...<b` and `*...=b` (`syntax:max ("*..." term)`, the bound a whole term, so
/// `f *...n + 1` is `f (*...(n + 1))`), `a...*` and `a<...*` (`syntax:max (term "...*")`, the argument
/// before them) and `*...*`.
const UNBOUNDED_RANGES: &[Accepted] = &[
    Accepted {
        source: "def sr1 (n : Nat) : List Nat := (*...n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term*..._» "*..." `n) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr2 (n : Nat) : List Nat := (*...=n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term*...=_» "*...=" `n) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr3 (n : Nat) : List Nat := (*...<n).toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Std.«term*...<_» "*...<" `n) ")") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr4 (n : Nat) : Std.Rci Nat := n...*",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Std.Rci [`Nat]))]) (Command.declValSimple ":=" (Std.«term_...*» `n "...*") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr5 (n : Nat) : Std.Roi Nat := n<...*",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Std.Roi [`Nat]))]) (Command.declValSimple ":=" (Std.«term_<...*» `n "<...*") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr6 : Std.Rii Nat := *...*",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr6 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Std.Rii [`Nat]))]) (Command.declValSimple ":=" (Std.«term*...*» "*...*") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr7 (xs : Array Nat) (n : Nat) : List Nat := xs[*...n].toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr7 []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj («term__[_]» `xs "[" (Std.«term*..._» "*..." `n) "]") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr8 (xs : Array Nat) (n : Nat) : List Nat := xs[n...*].toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr8 []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj («term__[_]» `xs "[" (Std.«term_...*» `n "...*") "]") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr9 (xs : Array Nat) (n : Nat) : List Nat := xs[n<...*].toList",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr9 []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.proj («term__[_]» `xs "[" (Std.«term_<...*» `n "<...*") "]") "." `toList) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def sr10 (f : Std.Rio Nat → Nat) (n : Nat) : Nat := f *...n + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `sr10 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow (Term.app `Std.Rio [`Nat]) "→" `Nat)] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `f [(Std.«term*..._» "*..." («term_+_» `n "+" (num "1")))]) (Termination.suffix [] []) []) []))"#,
    },
];

/// A do-level `have` (`doHave := "have" letConfig letDecl`): named, anonymous (`have : T := v` binds
/// `this` through `letId`'s `hygieneInfo`), a pattern (`letPatDecl`), inside a match arm or a branch,
/// or before a `;`.
const DO_HAVE: &[Accepted] = &[
    Accepted {
        source: "def hv1 (n : Nat) : Id Nat := do\n  match n with\n  | 0 => pure 0\n  | k+1 =>\n    have h : k < k + 1 := Nat.lt_succ_self k\n    pure k",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `hv1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doMatch "match" [] [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "0")])) [])])) (Term.matchAlt "|" [[(«term_+_» `k "+" (num "1"))]] "=>" (Term.doSeqIndent [(Term.doSeqItem (Term.doHave "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" («term_<_» `k "<" («term_+_» `k "+" (num "1"))))] ":=" (Term.app `Nat.lt_succ_self [`k])))) []) (Term.doSeqItem (Term.doExpr (Term.app `pure [`k])) [])]))])) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def hv2 (n : Nat) : Id Nat := do\n  have h : n = n := rfl\n  pure n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `hv2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doHave "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" («term_=_» `n "=" `n))] ":=" `rfl))) []) (Term.doSeqItem (Term.doExpr (Term.app `pure [`n])) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def hv3 (n : Nat) : Id Nat := do\n  if h : n < 5 then\n    have : n < 6 := Nat.lt_succ_of_lt h\n    pure n\n  else\n    pure 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `hv3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doIf "if" (Term.doIfProp [`h ":"] («term_<_» `n "<" (num "5"))) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doHave "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [(Term.typeSpec ":" («term_<_» `n "<" (num "6")))] ":=" (Term.app `Nat.lt_succ_of_lt [`h])))) []) (Term.doSeqItem (Term.doExpr (Term.app `pure [`n])) [])]) [] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [(num "0")])) [])])]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def hv4 (p : Nat × Nat) : Id Nat := do\n  have ⟨a, b⟩ := p\n  pure (a + b)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `hv4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doHave "have" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`a "," `b] "⟩") [] [] ":=" `p))) []) (Term.doSeqItem (Term.doExpr (Term.app `pure [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `a "+" `b) ")")])) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def hv5 (n : Nat) : Id Nat := do\n  have := Nat.le_refl n\n  pure n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `hv5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doHave "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId (hygieneInfo `[anonymous])) [] [] ":=" (Term.app `Nat.le_refl [`n])))) []) (Term.doSeqItem (Term.doExpr (Term.app `pure [`n])) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def hv6 (n : Nat) : Id Nat := do\n  have h : n = n := rfl; pure n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `hv6 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doHave "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" («term_=_» `n "=" `n))] ":=" `rfl))) [";"]) (Term.doSeqItem (Term.doExpr (Term.app `pure [`n])) [])])) (Termination.suffix [] []) []) []))"#,
    },
];

/// A `where` declaration's termination hints (`letRecDecl`'s `Termination.suffix`), which end its value
/// and stay with it at the declaration column; and the root well-founded recursion tactics
/// (`Init/WFTactics.lean`: `simp_wf`, `clean_wf`, `decreasing_trivial`, `decreasing_trivial_pre_omega`,
/// `decreasing_tactic`, each `tacticW`).
const WHERE_TERMINATION: &[Accepted] = &[
    Accepted {
        source: "def tb1 (n : Nat) : Nat := go 0 where\n  go (i : Nat) : Nat :=\n    if i < n then go (i+1) else i\n  termination_by n - i",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tb1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app `go [(num "0")]) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" (termIfThenElse "if" («term_<_» `i "<" `n) "then" (Term.app `go [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `i "+" (num "1")) ")")]) "else" `i))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] («term_-_» `n "-" `i))] []))] [])]) []))"#,
    },
    Accepted {
        source: "def tb2 (n : Nat) : Id Nat := go 0 where\n  go (i : Nat) : Id Nat := do\n    if h : i < n then go (i+1) else pure i\n  termination_by n - i\n  decreasing_by omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tb2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.app `go [(num "0")]) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))] ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doIf "if" (Term.doIfProp [`h ":"] («term_<_» `i "<" `n)) "then" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `go [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `i "+" (num "1")) ")")])) [])]) [] ["else" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr (Term.app `pure [`i])) [])])]) [])])))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] («term_-_» `n "-" `i))] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))]))] [])]) []))"#,
    },
    Accepted {
        source: "def tb4 (n : Nat) : Nat := go 0 + stop 0 where\n  go (i : Nat) : Nat :=\n    if i < n then go (i+1) else i\n  termination_by n - i\n  stop (i : Nat) : Nat := i",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tb4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (Term.app `go [(num "0")]) "+" (Term.app `stop [(num "0")])) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" (termIfThenElse "if" («term_<_» `i "<" `n) "then" (Term.app `go [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `i "+" (num "1")) ")")]) "else" `i))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] («term_-_» `n "-" `i))] [])) [] (Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `stop) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `i)) (Termination.suffix [] []))] [])]) []))"#,
    },
    Accepted {
        source: "def wf1 (n : Nat) : Nat := if h : n = 0 then 0 else wf1 (n - 1)\n  termination_by n\n  decreasing_by decreasing_trivial_pre_omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wf1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `wf1 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")])) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticDecreasing_trivial_pre_omega "decreasing_trivial_pre_omega")])))]) []) []))"#,
    },
    Accepted {
        source: "def wf2 (n : Nat) : Nat := if h : n = 0 then 0 else wf2 (n - 1)\n  termination_by n\n  decreasing_by simp_wf; decreasing_trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wf2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `wf2 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")])) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticSimp_wf "simp_wf") ";" (tacticDecreasing_trivial "decreasing_trivial")])))]) []) []))"#,
    },
    Accepted {
        source: "def wf3 (n : Nat) : Nat := if h : n = 0 then 0 else wf3 (n - 1)\n  termination_by n\n  decreasing_by decreasing_tactic",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wf3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `wf3 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")])) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticDecreasing_tactic "decreasing_tactic")])))]) []) []))"#,
    },
    Accepted {
        source: "def wf4 (n : Nat) : Nat := if h : n = 0 then 0 else wf4 (n - 1)\n  termination_by n\n  decreasing_by clean_wf; omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wf4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `wf4 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")])) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticClean_wf "clean_wf") ";" (Tactic.omega "omega" (Tactic.optConfig []))])))]) []) []))"#,
    },
];

/// A term `let rec` declaration's termination hints (`letRecDecl`'s `Termination.suffix`): a
/// `termination_by` or `decreasing_by` at depth 0 ends the declaration's value, deeper than the `let`
/// or at its column.
const LET_REC_TERMINATION: &[Accepted] = &[
    Accepted {
        source: "def lr1 (bs : Array Nat) : List Nat :=\n  let rec loop (i : Nat) (r : List Nat) :=\n    if i < bs.size then\n      loop (i+1) (bs[i]! :: r)\n    else\n      r.reverse\n    termination_by bs.size - i\n    decreasing_by decreasing_trivial_pre_omega\n  loop 0 []",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lr1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`bs] [":" (Term.app `Array [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `loop) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [`r] [":" (Term.app `List [`Nat])] [] ")")] [] ":=" (termIfThenElse "if" («term_<_» `i "<" `bs.size) "then" (Term.app `loop [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `i "+" (num "1")) ")") (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_::_» («term__[_]_!» `bs (group) "[" `i "]" (group) "!") "::" `r) ")")]) "else" `r.reverse))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] («term_-_» `bs.size "-" `i))] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticDecreasing_trivial_pre_omega "decreasing_trivial_pre_omega")])))]))]) [] (Term.app `loop [(num "0") («term[_]» "[" [] "]")])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lr2 (n : Nat) : Nat :=\n  let rec go (i : Nat) : Nat :=\n    if i < n then go (i + 1) else i\n  termination_by n - i\n  go 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lr2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" (termIfThenElse "if" («term_<_» `i "<" `n) "then" (Term.app `go [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `i "+" (num "1")) ")")]) "else" `i))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] («term_-_» `n "-" `i))] []))]) [] (Term.app `go [(num "0")])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def lr3 (n : Nat) : Nat :=\n  let rec go (i : Nat) : Nat := if i < n then go (i + 1) else i\n    decreasing_by omega\n  go 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lr3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `go) [(Term.explicitBinder "(" [`i] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" (termIfThenElse "if" («term_<_» `i "<" `n) "then" (Term.app `go [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `i "+" (num "1")) ")")]) "else" `i))) (Termination.suffix [] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))]))]) [] (Term.app `go [(num "0")])) (Termination.suffix [] []) []) []))"#,
    },
];

/// A `decreasing_by` in a `let rec` value owns the `;`s after it, as `by` does: `decreasing_by simp_wf;
/// decreasing_trivial_pre_omega` is one tactic sequence, and the body starts on the next line, never
/// after that `;`.
const LET_REC_DECREASING_BLOCK: &[Accepted] = &[Accepted {
    source: "def lrd1 (as : Array Nat) (p : Nat → Bool) : Option Nat :=\n  let rec loop (j : Nat) :=\n    if h : j < as.size then\n      if p as[j] then some j else loop (j + 1)\n    else none\n    decreasing_by simp_wf; decreasing_trivial_pre_omega\n  loop 0",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `lrd1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`as] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`p] [":" (Term.arrow `Nat "→" `Bool)] [] ")")] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `loop) [(Term.explicitBinder "(" [`j] [":" `Nat] [] ")")] [] ":=" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_<_» `j "<" `as.size) "then" (termIfThenElse "if" (Term.app `p [(«term__[_]» `as "[" `j "]")]) "then" (Term.app `some [`j]) "else" (Term.app `loop [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `j "+" (num "1")) ")")])) "else" `none))) (Termination.suffix [] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(tacticSimp_wf "simp_wf") ";" (tacticDecreasing_trivial_pre_omega "decreasing_trivial_pre_omega")])))]))]) [] (Term.app `loop [(num "0")])) (Termination.suffix [] []) []) []))"#,
}];

/// A `by` body followed by a termination hint on a later line: at the tactics' column the hint passes
/// `sepByIndent`'s `checkColEq`, so the sequence keeps a trailing empty separator
/// (`allowTrailingSep`); at another column it does not.
const TRAILING_TACTIC_SEPARATOR: &[Accepted] = &[
    Accepted {
        source: "def tt1 (n : Nat) : Nat := by\n  exact if h : n = 0 then 0 else tt1 (n - 1)\n  termination_by n\n  decreasing_by omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tt1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `tt1 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")]))) []]))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] [(Termination.decreasingBy "decreasing_by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))]) []) []))"#,
    },
    Accepted {
        source: "def tt2 (n : Nat) : Nat := by\n  exact if h : n = 0 then 0 else tt2 (n - 1)\n  termination_by n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tt2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `tt2 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")]))) []]))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] []) []) []))"#,
    },
    Accepted {
        source: "def tt3 (n : Nat) : Nat := by\n    exact if h : n = 0 then 0 else tt3 (n - 1)\n  termination_by n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tt3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (termDepIfThenElse "if" (Lean.binderIdent `h) ":" («term_=_» `n "=" (num "0")) "then" (num "0") "else" (Term.app `tt3 [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_-_» `n "-" (num "1")) ")")])))]))) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] []) []) []))"#,
    },
];

/// `e matches p | q` (`Lean.«term_Matches_|»`, `syntax:50 term:51 " matches " sepBy1(term:51, " | ")`):
/// the patterns as `sepBy1`'s node, the `|`s on the `matches` line its own, inside `||` and brackets.
const MATCHES_NOTATION: &[Accepted] = &[
    Accepted {
        source: "def mt1 (c : Char) : Bool :=\n  (c matches '!' | '#' | '$' | '%' | '&' | '\\'' | '*' | '+' | '-' | '.' | '^' | '_' | '`' | '|' | '~') ||\n  c.isAlpha",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Char] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" («term_||_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Lean.«term_Matches_|» `c "matches" [(char "'!'") "|" (char "'#'") "|" (char "'$'") "|" (char "'%'") "|" (char "'&'") "|" (char "'\\''") "|" (char "'*'") "|" (char "'+'") "|" (char "'-'") "|" (char "'.'") "|" (char "'^'") "|" (char "'_'") "|" (char "'`'") "|" (char "'|'") "|" (char "'~'")]) ")") "||" `c.isAlpha) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def mt2 (c : Char) : Bool :=\n  c matches ' ' | '\\t'",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Char] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" (Lean.«term_Matches_|» `c "matches" [(char "' '") "|" (char "'\\t'")]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def mt3 (c : Char) (b : Bool) : Bool := b || (c matches ' ' | '\\t')",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`c] [":" `Char] [] ")") (Term.explicitBinder "(" [`b] [":" `Bool] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" («term_||_» `b "||" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Lean.«term_Matches_|» `c "matches" [(char "' '") "|" (char "'\\t'")]) ")")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def mt4 (o : Option Nat) : Bool := o matches some (_ + 1) | none",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`o] [":" (Term.app `Option [`Nat])] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" (Lean.«term_Matches_|» `o "matches" [(Term.app `some [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.hole "_") "+" (num "1")) ")")]) "|" `none]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def mt5 (xs : List Nat) : Bool := xs matches _ :: _ :: _",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `mt5 []) (Command.optDeclSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")")] [(Term.typeSpec ":" `Bool)]) (Command.declValSimple ":=" (Lean.«term_Matches_|» `xs "matches" [(«term_::_» (Term.hole "_") "::" («term_::_» (Term.hole "_") "::" (Term.hole "_")))]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem mt6 (P : Option Nat → Prop) (hp : ∀ s, P s → s matches some ..) : True := trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `mt6 []) (Command.declSig [(Term.explicitBinder "(" [`P] [":" (Term.arrow (Term.app `Option [`Nat]) "→" (Term.prop "Prop"))] [] ")") (Term.explicitBinder "(" [`hp] [":" (Term.forall "∀" [`s] [] "," (Term.arrow (Term.app `P [`s]) "→" (Lean.«term_Matches_|» `s "matches" [(Term.app `some [(Term.ellipsis "..")])])))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" `trivial (Termination.suffix [] []) [])))"#,
    },
];

/// An instance after attributes (`@[always_inline] instance …`, `@[default_instance]`, with a
/// visibility): `declModifiers`' attributes, as for a definition. The elaborator refuses them, as it
/// refuses every attribute but a global `simp`.
const ATTRIBUTED_INSTANCES: &[Accepted] = &[
    Accepted {
        source: "@[always_inline]\ninstance : Inhabited Nat := ⟨0⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `always_inline []))] "]")] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0")] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[inline] instance : Inhabited Bool := ⟨true⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `inline []))] "]")] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Bool]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [`true] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[default_instance] instance : Inhabited String := ⟨\"\"⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.default_instance "default_instance" []))] "]")] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`String]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(str "\"\"")] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "@[always_inline]\ninstance foo : Inhabited Nat where\n  default := 0",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `always_inline []))] "]")] [] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [(Command.declId `foo [])] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.whereStructInst "where" (Term.structInstFields [(Term.structInstField (Term.structInstLVal `default []) [[] [] (Term.structInstFieldDef ":=" [] (num "0"))])]) [])))"#,
    },
    Accepted {
        source: "@[no_expose]\npublic instance : Inhabited Nat := ⟨1⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `no_expose []))] "]")] [(Command.public "public")] [] [] [] []) (Command.instance (Term.attrKind []) "instance" [] [] (Command.declSig [] (Term.typeSpec ":" (Term.app `Inhabited [`Nat]))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "1")] "⟩") (Termination.suffix [] []) [])))"#,
    },
];

/// The coercion arrow `↑x` (`syntax:max "↑" term:max : term`, `coeNotation` at the root, `Init/Coe.lean`):
/// a prefix on one atomic term, so `↑m + ↑n` is `(↑m) + (↑n)` and `f ↑n` applies `f` to `↑n`.
const COERCION_ARROW: &[Accepted] = &[
    Accepted {
        source: "theorem co1 {n : Nat} {z : Int} : (↑n : Int) = z ↔ z = n := by\n  constructor <;> intro h <;> exact h.symm",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `co1 []) (Command.declSig [(Term.implicitBinder "{" [`n] [":" `Nat] "}") (Term.implicitBinder "{" [`z] [":" `Int] "}")] (Term.typeSpec ":" («term_↔_» («term_=_» (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (coeNotation "↑" `n) ":" [`Int] ")") "=" `z) "↔" («term_=_» `z "=" `n)))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`h])) "<;>" (Tactic.exact "exact" `h.symm))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem co2 (m n : Nat) : (↑(m + n) : Int) = ↑m + ↑n := by\n  simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `co2 []) (Command.declSig [(Term.explicitBinder "(" [`m `n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (coeNotation "↑" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `m "+" `n) ")")) ":" [`Int] ")") "=" («term_+_» (coeNotation "↑" `m) "+" (coeNotation "↑" `n))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def co3 (n : Nat) : Int := ↑n + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `co3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Int)]) (Command.declValSimple ":=" («term_+_» (coeNotation "↑" `n) "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def co4 (f : Nat → Int) (n : Nat) : Int := f ↑n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `co4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Int)] [] ")") (Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Int)]) (Command.declValSimple ":=" (Term.app `f [(coeNotation "↑" `n)]) (Termination.suffix [] []) []) []))"#,
    },
];

/// `f $ x` (`syntax:min term atomic(" $" ws) term:min`, `«term_$__»`): `<|`'s other spelling, right-associative
/// at the lowest precedence, so `f $ x + 1` is `f (x + 1)` and `Option $ List $ α` nests rightward.
const DOLLAR_PIPELINE: &[Accepted] = &[
    Accepted {
        source: "structure Dl (α : Type) where\n  comm : Option $ List $ Option α",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.structure (Command.structureTk "structure") (Command.declId `Dl []) (Command.optDeclSig [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [])] [] ")")] []) [] ["where" [] (Command.structFields [(Command.structSimpleBinder (Command.declModifiers [] [] [] [] [] [] []) `comm (Command.optDeclSig [] [(Term.typeSpec ":" («term_$__» `Option "$" («term_$__» `List "$" (Term.app `Option [`α]))))]) [])])] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "theorem dl2 (a : Nat) (h : a = 1) : a = 1 := id $ h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `dl2 []) (Command.declSig [(Term.explicitBinder "(" [`a] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" (num "1")))) (Command.declValSimple ":=" («term_$__» `id "$" `h) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def dl3 (f : Nat → Nat) (x : Nat) : Nat := f $ x + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `dl3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_$__» `f "$" («term_+_» `x "+" (num "1"))) (Termination.suffix [] []) []) []))"#,
    },
];

/// A `let rec` declaration's `termination_by` before the `;` that ends the local definition.
const LET_REC_SEMICOLON_TERMINATION: &[Accepted] = &[Accepted {
    source: "def n : Nat := let rec f (n : Nat) : Nat := n termination_by n; f 0",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `n []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `f) [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" `n)) (Termination.suffix [(Termination.terminationBy "termination_by" [] [] `n)] []))]) ";" (Term.app `f [(num "0")])) (Termination.suffix [] []) []) []))"#,
}];

/// Calculation steps after a first step on the `calc` line: their position is the first later line's
/// column, at or left of the first step, with or without `_`, and the enclosing tactic line after
/// several steps ends them.
const CALC_STEP_POSITIONS: &[Accepted] = &[
    Accepted {
        source: "theorem ct3 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc a = b := h1\n    _ = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ct3 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.calcTactic "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ct4 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  have h : a = c := by\n    calc a = b := h1\n      _ = c := h2\n  exact h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ct4 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `h) [] [(Term.typeSpec ":" («term_=_» `a "=" `c))] ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.calcTactic "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» (Term.hole "_") "=" `c) ":=" `h2)]))])))))) [] (Tactic.exact "exact" `h)]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem ct6 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc a = b := h1\n  b = c := h2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `ct6 []) (Command.declSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h1] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`h2] [":" («term_=_» `b "=" `c)] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" `c))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Lean.calcTactic "calc" (Lean.calcSteps (Lean.calcFirstStep («term_=_» `a "=" `b) [":=" `h1]) [(Lean.calcStep («term_=_» `b "=" `c) ":=" `h2)]))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A definition's `deriving` clause (`optDefDeriving`, `"deriving " notSymbol("instance")
/// sepBy1(ident, ", ")`), on the value's line or the next: its classes end the value.
const DEFINITION_DERIVING: &[Accepted] = &[
    Accepted {
        source: "def DerA := Nat\n  deriving Repr, BEq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `DerA []) (Command.optDeclSig [] []) (Command.declValSimple ":=" `Nat (Termination.suffix [] []) []) ["deriving" [(Command.derivingClass [] `Repr) "," (Command.derivingClass [] `BEq)]]))"#,
    },
    Accepted {
        source: "def DerB : Type := Array Nat deriving Inhabited",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `DerB []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.type "Type" []))]) (Command.declValSimple ":=" (Term.app `Array [`Nat]) (Termination.suffix [] []) []) ["deriving" [(Command.derivingClass [] `Inhabited)]]))"#,
    },
    Accepted {
        source: "def DerC (n : Nat) : Nat := n + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `DerC []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» `n "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
];

/// A `while` loop in `do` (`Term.doWhile`, `"while " (ident " : ")? termBeforeDo " do " doSeq`): its
/// condition a `doIfProp`, with or without evidence, and its body a sequence of the surrounding scope.
const DO_WHILE: &[Accepted] = &[
    Accepted {
        source: "def wl1 (n : Nat) : Id Nat := do\n  let mut i := 0\n  while i < n do\n    i := i + 1\n  return i",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wl1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `i) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doWhile "while" (Term.doIfProp [] («term_<_» `i "<" `n)) "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `i) [] [] ":=" («term_+_» `i "+" (num "1")))) [])])) []) (Term.doSeqItem (Term.doReturn "return" [`i]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def wl2 (n : Nat) : Id Nat := do\n  let mut i := 0\n  while h : i < n do\n    i := i + 1\n  return i",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `wl2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `i) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doWhile "while" (Term.doIfProp [`h ":"] («term_<_» `i "<" `n)) "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReassign (Term.letIdDeclNoBinders (Term.letId `i) [] [] ":=" («term_+_» `i "+" (num "1")))) [])])) []) (Term.doSeqItem (Term.doReturn "return" [`i]) [])])) (Termination.suffix [] []) []) []))"#,
    },
];

/// An `inductive` after declaration modifiers (`private`, `public`, `protected`, attributes, a doc):
/// the modifiers' node is built as a definition's.
const INDUCTIVE_MODIFIERS: &[Accepted] = &[
    Accepted {
        source: "private inductive Ia where\n  | a | b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.private "private")] [] [] [] []) (Command.inductive "inductive" (Command.declId `Ia []) (Command.optDeclSig [] []) ["where"] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `a (Command.optDeclSig [] [])) (Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `b (Command.optDeclSig [] []))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "public inductive Ib (α : Type) where\n  | mk (x : α)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [(Command.public "public")] [] [] [] []) (Command.inductive "inductive" (Command.declId `Ib []) (Command.optDeclSig [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [])] [] ")")] []) ["where"] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `mk (Command.optDeclSig [(Term.explicitBinder "(" [`x] [":" `α] [] ")")] []))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "@[simp] inductive Ic where\n  | c",
        tree: r#"(Command.declaration (Command.declModifiers [] [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] [] []))] "]")] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `Ic []) (Command.optDeclSig [] []) ["where"] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `c (Command.optDeclSig [] []))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "/-- doc -/\ninductive Id2 where\n  | d",
        tree: r#"(Command.declaration (Command.declModifiers [(Command.docComment "/--" "doc -/")] [] [] [] [] [] []) (Command.inductive "inductive" (Command.declId `Id2 []) (Command.optDeclSig [] []) ["where"] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `d (Command.optDeclSig [] []))] [] (Command.optDeriving [])))"#,
    },
    Accepted {
        source: "protected inductive Ie where\n  | e",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [(Command.protected "protected")] [] [] []) (Command.inductive "inductive" (Command.declId `Ie []) (Command.optDeclSig [] []) ["where"] [(Command.ctor [] "|" (Command.declModifiers [] [] [] [] [] [] []) `e (Command.optDeclSig [] []))] [] (Command.optDeriving [])))"#,
    },
];

/// A pattern's update in `do` (`(a, b) := e`, `(a, b) ← e`): `doReassign`'s `letPatDecl` and
/// `doReassignArrow`'s `doPatDecl`.
const PATTERN_REASSIGNMENT: &[Accepted] = &[
    Accepted {
        source: "def tr1 (n : Nat) : Id Nat := do\n  let mut a := 0\n  let mut b := 0\n  (a, b) := (n, n + 1)\n  return a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tr1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `a) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `b) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doReassign (Term.letPatDecl (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") [] [] ":=" (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`n "," [(«term_+_» `n "+" (num "1"))]] ")"))) []) (Term.doSeqItem (Term.doReturn "return" [(«term_+_» `a "+" `b)]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def tr2 (n : Nat) : Id Nat := do\n  let mut a := 0\n  let mut b := 0\n  (a, b) ← pure (n, n)\n  return a + b",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `tr2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `a) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doLet "let" ["mut"] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `b) [] [] ":=" (num "0")))) []) (Term.doSeqItem (Term.doReassignArrow (Term.doPatDecl (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") [] "←" (Term.doExpr (Term.app `pure [(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`n "," [`n]] ")")])) [])) []) (Term.doSeqItem (Term.doReturn "return" [(«term_+_» `a "+" `b)]) [])])) (Termination.suffix [] []) []) []))"#,
    },
];

/// A tactic `have`/`let` whose declaration is a pattern (`have ⟨k, hk⟩ := h`, `let ⟨a, b⟩ := p`):
/// the term forms' `letPatDecl`.
const TACTIC_PATTERN_BINDINGS: &[Accepted] = &[
    Accepted {
        source: "theorem th1 (h : ∃ k, k = 1) : True := by\n  have ⟨k, hk⟩ := h\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `th1 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [])) "," («term_=_» `k "=" (num "1")))] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticHave__ "have" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`k "," `hk] "⟩") [] [] ":=" `h))) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem th2 (p : Nat × Nat) : True := by\n  let ⟨a, b⟩ := p\n  trivial",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `th2 []) (Command.declSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticLet__ "let" (Term.letConfig []) (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`a "," `b] "⟩") [] [] ":=" `p))) [] (Tactic.tacticTrivial "trivial")]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A projection touching a named argument projects the whole application: `f (l := 1).1 H` is
/// `(f (l := 1)).1 H`, a named argument being no term a trailing parser extends.
const NAMED_ARGUMENT_PROJECTION: &[Accepted] = &[Accepted {
    source: "def nq (f : (l : Nat) → (Nat → Nat) × Nat) (H : Nat) : Nat := f (l := 1).1 H",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `nq []) (Command.optDeclSig [(Term.explicitBinder "(" [`f] [":" (Term.depArrow (Term.explicitBinder "(" [`l] [":" `Nat] [] ")") "→" («term_×_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow `Nat "→" `Nat) ")") "×" `Nat))] [] ")") (Term.explicitBinder "(" [`H] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.app (Term.proj (Term.app `f [(Term.namedArgument "(" `l ":=" (num "1") ")")]) "." (fieldIdx "1")) [`H]) (Termination.suffix [] []) []) []))"#,
}];

/// A `by` in a local's value owns the `;`s after it only until its block ends: the next match
/// alternative ends it, so the `;` after `| .succ j => (by rfl)` is the local's separator.
const BY_BLOCK_ENDS_AT_AN_ALTERNATIVE: &[Accepted] = &[Accepted {
    source: "theorem reflexive2 (n : Nat) : n = n := let rec proof (k : Nat) : k = k := match k with | .zero => by rfl | .succ j => (by rfl); proof n",
    tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `reflexive2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `n "=" `n))) (Command.declValSimple ":=" (Term.letrec (group "let" "rec") (Term.letRecDecls [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `proof) [(Term.explicitBinder "(" [`k] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_=_» `k "=" `k))] ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `k)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.dotIdent "." `zero)]] "=>" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))) (Term.matchAlt "|" [[(Term.app (Term.dotIdent "." `succ) [`j])]] "=>" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) ")"))])))) (Termination.suffix [] []))]) ";" (Term.app `proof [`n])) (Termination.suffix [] []) [])))"#,
}];

/// Subtypes: a binder, an optional type, `//` and the predicate.
const SUBTYPES: &[Accepted] = &[
    Accepted {
        source: "def z3 (p : Nat → Prop) : Type := {x // p x}",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `z3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" (Term.arrow `Nat "→" (Term.prop "Prop"))] [] ")")] [(Term.typeSpec ":" (Term.type "Type" []))]) (Command.declValSimple ":=" («term{_:_//_}» "{" `x [] "//" (Term.app `p [`x]) "}") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def z6 (p : Nat → Prop) : Type := {x : Nat // p x ∧ x = 0}",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `z6 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" (Term.arrow `Nat "→" (Term.prop "Prop"))] [] ")")] [(Term.typeSpec ":" (Term.type "Type" []))]) (Command.declValSimple ":=" («term{_:_//_}» "{" `x [":" `Nat] "//" («term_∧_» (Term.app `p [`x]) "∧" («term_=_» `x "=" (num "0"))) "}") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "noncomputable def z7 {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} := Classical.indefiniteDescription p h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [(Command.noncomputable "noncomputable")] [] []) (Command.definition "def" (Command.declId `z7 []) (Command.optDeclSig [(Term.implicitBinder "{" [`α] [":" (Term.sort "Sort" [`u])] "}") (Term.explicitBinder "(" [`p] [":" (Term.arrow `α "→" (Term.prop "Prop"))] [] ")") (Term.explicitBinder "(" [`h] [":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [])) "," (Term.app `p [`x]))] [] ")")] [(Term.typeSpec ":" («term{_:_//_}» "{" `x [] "//" (Term.app `p [`x]) "}"))]) (Command.declValSimple ":=" (Term.app `Classical.indefiniteDescription [`p `h]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def z8 (n : Nat) : Type := { s : Nat // s < n }",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `z8 []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" (Term.type "Type" []))]) (Command.declValSimple ":=" («term{_:_//_}» "{" `s [":" `Nat] "//" («term_<_» `s "<" `n) "}") (Termination.suffix [] []) []) []))"#,
    },
];

/// A nested action `(← e)`: `Term.nestedAction` over the action as a `doExpr`.
const NESTED_ACTIONS: &[Accepted] = &[
    Accepted {
        source: "def n1 (g : Id Nat) : Id Nat := do let x := (← g) + 1; return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `n1 []) (Command.optDeclSig [(Term.explicitBinder "(" [`g] [":" (Term.app `Id [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLet "let" [] (Term.letConfig []) (Term.letDecl (Term.letIdDecl (Term.letId `x) [] [] ":=" («term_+_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.nestedAction "←" (Term.doExpr `g)) ")") "+" (num "1"))))) [";"]) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def n2 (g : Id Nat) : Id Nat := do return (← g)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `n2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`g] [":" (Term.app `Id [`Nat])] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doReturn "return" [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.nestedAction "←" (Term.doExpr `g)) ")")]) [])])) (Termination.suffix [] []) []) []))"#,
    },
];

/// Array literals: a list literal's shape under `«term#[_,]»`.
const ARRAYS: &[Accepted] = &[
    Accepted {
        source: "def a1 : Array Nat := #[]",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `a1 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Array [`Nat]))]) (Command.declValSimple ":=" («term#[_,]» "#[" [] "]") (Termination.suffix [] []) []) []))"##,
    },
    Accepted {
        source: "def a2 : Array Nat := #[1, 2, 3]",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `a2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Array [`Nat]))]) (Command.declValSimple ":=" («term#[_,]» "#[" [(num "1") "," (num "2") "," (num "3")] "]") (Termination.suffix [] []) []) []))"##,
    },
    Accepted {
        source: "def a3 : Array Nat := #[1, 2,]",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `a3 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Array [`Nat]))]) (Command.declValSimple ":=" («term#[_,]» "#[" [(num "1") "," (num "2") ","] "]") (Termination.suffix [] []) []) []))"##,
    },
    Accepted {
        source: "theorem a4 : #[1, 2].size = 2 := rfl",
        tree: r##"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `a4 []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.proj («term#[_,]» "#[" [(num "1") "," (num "2")] "]") "." `size) "=" (num "2")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"##,
    },
];

/// Tuples: the first element, then the rest separated, a trailing comma allowed.
const TUPLES: &[Accepted] = &[
    Accepted {
        source: "theorem t1 (a b : Nat) : (a, b).1 = a := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» (Term.proj (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") "." (fieldIdx "1")) "=" `a))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def t2 (a b c : Nat) : Nat × Nat × Nat := (a, b, c)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t2 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_×_» `Nat "×" («term_×_» `Nat "×" `Nat)))]) (Command.declValSimple ":=" (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b "," `c]] ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def t3 (a b c : Nat) : (Nat × Nat) × Nat := ((a, b), c)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t3 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b `c] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_×_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")") "×" `Nat))]) (Command.declValSimple ":=" (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b]] ")") "," [`c]] ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def t4 (a b : Nat) : Nat × Nat := (a, b,)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t4 []) (Command.optDeclSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")")] [(Term.typeSpec ":" («term_×_» `Nat "×" `Nat))]) (Command.declValSimple ":=" (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`a "," [`b ","]] ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def t5 : List (Nat × Nat) := [(1, 2), (3, 4)]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t5 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `List [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")]))]) (Command.declValSimple ":=" («term[_]» "[" [(Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(num "1") "," [(num "2")]] ")") "," (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(num "3") "," [(num "4")]] ")")] "]") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def work (pair : Id (Nat × Nat)) : Id Nat := do let (x, y) ← pair; return x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `work []) (Command.optDeclSig [(Term.explicitBinder "(" [`pair] [":" (Term.app `Id [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_×_» `Nat "×" `Nat) ")")])] [] ")")] [(Term.typeSpec ":" (Term.app `Id [`Nat]))]) (Command.declValSimple ":=" (Term.do "do" (Term.doSeqIndent [(Term.doSeqItem (Term.doLetArrow "let" [] (Term.letConfig []) (Term.doPatDecl (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [`x "," [`y]] ")") [] "←" (Term.doExpr `pair) [])) [";"]) (Term.doSeqItem (Term.doReturn "return" [`x]) [])])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def t6 (p : Nat × Nat) : Nat × Nat := (p.2, p.1)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `t6 []) (Command.optDeclSig [(Term.explicitBinder "(" [`p] [":" («term_×_» `Nat "×" `Nat)] [] ")")] [(Term.typeSpec ":" («term_×_» `Nat "×" `Nat))]) (Command.declValSimple ":=" (Term.tuple (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) [(Term.proj `p "." (fieldIdx "2")) "," [(Term.proj `p "." (fieldIdx "1"))]] ")") (Termination.suffix [] []) []) []))"#,
    },
];

/// A `[` touching the term before it indexes that term (`Init/GetElem.lean`); spaced, it is a
/// list argument. The index takes only the last argument, as `x6` shows.
const INDEXING: &[Accepted] = &[
    Accepted {
        source: "theorem x1 (f : List Nat → Nat) (h : ∀ l, f l = 0) : f[1] = 0 := h _",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `x1 []) (Command.declSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow (Term.app `List [`Nat]) "→" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`l] [] "," («term_=_» (Term.app `f [`l]) "=" (num "0")))] [] ")")] (Term.typeSpec ":" («term_=_» («term__[_]» `f "[" (num "1") "]") "=" (num "0")))) (Command.declValSimple ":=" (Term.app `h [(Term.hole "_")]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem x2 (f : List Nat → Nat) (h : ∀ l, f l = 0) : f [1] = 0 := h _",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `x2 []) (Command.declSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow (Term.app `List [`Nat]) "→" `Nat)] [] ")") (Term.explicitBinder "(" [`h] [":" (Term.forall "∀" [`l] [] "," («term_=_» (Term.app `f [`l]) "=" (num "0")))] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [(«term[_]» "[" [(num "1")] "]")]) "=" (num "0")))) (Command.declValSimple ":=" (Term.app `h [(Term.hole "_")]) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem x3 (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i] = xs[i] := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `x3 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")") (Term.explicitBinder "(" [`i] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» `i "<" `xs.size)] [] ")")] (Term.typeSpec ":" («term_=_» («term__[_]» `xs "[" `i "]") "=" («term__[_]» `xs "[" `i "]")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem x4 (xs : List Nat) : xs[0]? = xs.head? := by cases xs <;> rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `x4 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `List [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» («term__[_]_?» `xs (group) "[" (num "0") "]" (group) "?") "=" `xs.head?))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.elimTarget [] `xs)] [] []) "<;>" (Tactic.tacticRfl "rfl"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem x5 (xs : Array Nat) : xs[0]! = xs[0]! := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `x5 []) (Command.declSig [(Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» («term__[_]_!» `xs (group) "[" (num "0") "]" (group) "!") "=" («term__[_]_!» `xs (group) "[" (num "0") "]" (group) "!")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem x6 (f : Nat → Nat) (xs : Array Nat) : f xs[0]! = f (xs[0]!) := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `x6 []) (Command.declSig [(Term.explicitBinder "(" [`f] [":" (Term.arrow `Nat "→" `Nat)] [] ")") (Term.explicitBinder "(" [`xs] [":" (Term.app `Array [`Nat])] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [(«term__[_]_!» `xs (group) "[" (num "0") "]" (group) "!")]) "=" (Term.app `f [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term__[_]_!» `xs (group) "[" (num "0") "]" (group) "!") ")")])))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
];

/// `omega`, `unfold`, `split` and `rwa`, with and without locations.
const TACTIC_FORMS: &[Accepted] = &[
    Accepted {
        source: "theorem o1 (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» `a "<" `b)] [] ")")] (Term.typeSpec ":" («term_≤_» («term_+_» `a "+" (num "1")) "≤" `b))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem o2 (a b : Nat) (h : a < b) : a + 1 ≤ b ∧ True := ⟨by omega, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `o2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_<_» `a "<" `b)] [] ")")] (Term.typeSpec ":" («term_∧_» («term_≤_» («term_+_» `a "+" (num "1")) "≤" `b) "∧" `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))]))) "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u1 (n : Nat) (h : n = 0) : f n = 1 := by unfold f; simp [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `n "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [`n]) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.unfold "unfold" [`f] []) ";" (Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem u2 (n : Nat) (h : n = 0) : f n = 1 := by\n  unfold f at *\n  simp [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `u2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `n "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» (Term.app `f [`n]) "=" (num "1")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.unfold "unfold" [`f] [(Tactic.location "at" (Tactic.locationWildcard "*"))]) [] (Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem p1 (n : Nat) : f n ≠ 0 := by\n  unfold f\n  split <;> simp",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `p1 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_≠_» (Term.app `f [`n]) "≠" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.unfold "unfold" [`f] []) [] (Tactic.«tactic_<;>_» (Tactic.split "split" [] []) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem p2 (n : Nat) (h : f n = 0) : False := by\n  unfold f at h\n  split at h <;> simp at h",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `p2 []) (Command.declSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» (Term.app `f [`n]) "=" (num "0"))] [] ")")] (Term.typeSpec ":" `False)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.unfold "unfold" [`f] [(Tactic.location "at" (Tactic.locationHyp [`h]))]) [] (Tactic.«tactic_<;>_» (Tactic.split "split" [] [(Tactic.location "at" (Tactic.locationHyp [`h]))]) "<;>" (Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h]))]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem w1 (a b : Nat) (h : a = b) (g : b = 0) : a = 0 := by rwa [h]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w1 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`g] [":" («term_=_» `b "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» `a "=" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem w2 (a b : Nat) (h : a = b) (g : a = 0) : b = 0 := by rwa [h] at g",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `w2 []) (Command.declSig [(Term.explicitBinder "(" [`a `b] [":" `Nat] [] ")") (Term.explicitBinder "(" [`h] [":" («term_=_» `a "=" `b)] [] ")") (Term.explicitBinder "(" [`g] [":" («term_=_» `a "=" (num "0"))] [] ")")] (Term.typeSpec ":" («term_=_» `b "=" (num "0")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [(Tactic.location "at" (Tactic.locationHyp [`g]))])]))) (Termination.suffix [] []) [])))"#,
    },
];

/// Tactics on separate lines, and `·` focusing the main goal.
const TACTIC_BLOCKS: &[Accepted] = &[
    Accepted {
        source: "theorem c1 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  · exact hp\n  · exact hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c1 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hp)]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" `hq)])))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem c2 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  · skip\n    exact hp\n  · skip; exact hq",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `c2 []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`hp] [":" `p] [] ")") (Term.explicitBinder "(" [`hq] [":" `q] [] ")")] (Term.typeSpec ":" («term_∧_» `p "∧" `q))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.constructor "constructor") [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip") [] (Tactic.exact "exact" `hp)]))) [] (Lean.cdot (Lean.cdotTk "·") (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.skip "skip") ";" (Tactic.exact "exact" `hq)])))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// A `by` block inside a tactic's term argument. The pin parses every row; it refuses `s1`,
/// `s2` and `s4` only when elaborating them.
const NESTED_PROOFS: &[Accepted] = &[
    Accepted {
        source: "theorem s1 (x : Nat) : x = x := by simp only [by rfl]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s1 []) (Command.declSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `x "=" `x))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))))] "]"] [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem s2 : True := by simpa only [by rfl]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s2 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simpa "simpa" [] [] (Tactic.simpaArgsRest (Tactic.optConfig []) [] ["only"] [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))))] "]")] []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem s3 : True := by simpa using (by rfl)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s3 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simpa "simpa" [] [] (Tactic.simpaArgsRest (Tactic.optConfig []) [] [] [] ["using" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) ")")]))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem s4 : True := by simp_all only [by rfl]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s4 []) (Command.declSig [] (Term.typeSpec ":" `True)) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simpAll "simp_all" (Tactic.optConfig []) [] ["only"] ["[" [(Tactic.simpLemma [] [] (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))))] "]"])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem s5 (x : Nat) : x = x := by rw [show x = x by rfl]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `s5 []) (Command.declSig [(Term.explicitBinder "(" [`x] [":" `Nat] [] ")")] (Term.typeSpec ":" («term_=_» `x "=" `x))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.rwSeq "rw" (Tactic.optConfig []) (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.show "show" («term_=_» `x "=" `x) (Term.byTactic' "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))))] "]") [])]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem n1 (h : 1 = 1) : 1 = 1 ∧ 1 = 1 := by exact ⟨h, by rfl⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `n1 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" («term_=_» (num "1") "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» (num "1") "=" (num "1")) "∧" («term_=_» (num "1") "=" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.anonymousCtor "⟨" [`h "," (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")])))] "⟩"))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem n2 (h : 1 = 1) : 1 = 1 ∧ 1 = 1 := by\n  refine ⟨h, ?_⟩\n  exact (by rfl)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `n2 []) (Command.declSig [(Term.explicitBinder "(" [`h] [":" («term_=_» (num "1") "=" (num "1"))] [] ")")] (Term.typeSpec ":" («term_∧_» («term_=_» (num "1") "=" (num "1")) "∧" («term_=_» (num "1") "=" (num "1"))))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.refine "refine" (Term.anonymousCtor "⟨" [`h "," (Term.syntheticHole "?" "_")] "⟩")) [] (Tactic.exact "exact" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticRfl "rfl")]))) ")"))]))) (Termination.suffix [] []) [])))"#,
    },
];

/// `⟨…⟩` as a match pattern, nested or not.
const ANONYMOUS_CONSTRUCTOR_PATTERNS: &[Accepted] = &[
    Accepted {
        source: "theorem g (p q : Prop) (h : p ∧ q) : q ∧ p := match h with | ⟨hp, hq⟩ => ⟨hq, hp⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g []) (Command.declSig [(Term.explicitBinder "(" [`p `q] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" `q)] [] ")")] (Term.typeSpec ":" («term_∧_» `q "∧" `p))) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `h)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.anonymousCtor "⟨" [`hp "," `hq] "⟩")]] "=>" (Term.anonymousCtor "⟨" [`hq "," `hp] "⟩"))])) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem k (p q r : Prop) (h : p ∧ (q ∧ r)) : r := match h with | ⟨_, ⟨_, hr⟩⟩ => hr",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `k []) (Command.declSig [(Term.explicitBinder "(" [`p `q `r] [":" (Term.prop "Prop")] [] ")") (Term.explicitBinder "(" [`h] [":" («term_∧_» `p "∧" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_∧_» `q "∧" `r) ")"))] [] ")")] (Term.typeSpec ":" `r)) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `h)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [(Term.hole "_") "," `hr] "⟩")] "⟩")]] "=>" `hr)])) (Termination.suffix [] []) [])))"#,
    },
];

const DOTTED_IDENTIFIERS: &[Accepted] = &[
    Accepted {
        source: "def x : T := .leaf",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `x []) (Command.optDeclSig [] [(Term.typeSpec ":" `T)]) (Command.declValSimple ":=" (Term.dotIdent "." `leaf) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def y : T := .node .leaf (.node .leaf .leaf)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `y []) (Command.optDeclSig [] [(Term.typeSpec ":" `T)]) (Command.declValSimple ":=" (Term.app (Term.dotIdent "." `node) [(Term.dotIdent "." `leaf) (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app (Term.dotIdent "." `node) [(Term.dotIdent "." `leaf) (Term.dotIdent "." `leaf)]) ")")]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def z : Option Nat := .some 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `z []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Option [`Nat]))]) (Command.declValSimple ":=" (Term.app (Term.dotIdent "." `some) [(num "1")]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def f : Nat → T := fun _ => .leaf",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `T))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (Term.dotIdent "." `leaf))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def g : Nat → Option Nat := .some",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" (Term.app `Option [`Nat])))]) (Command.declValSimple ":=" (Term.dotIdent "." `some) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "theorem t : (T.node .leaf .leaf).size = 3 := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `T.node [(Term.dotIdent "." `leaf) (Term.dotIdent "." `leaf)]) ")") "." `size) "=" (num "3")))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def k : List T := [.leaf, .node .leaf .leaf]",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `k []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `List [`T]))]) (Command.declValSimple ":=" («term[_]» "[" [(Term.dotIdent "." `leaf) "," (Term.app (Term.dotIdent "." `node) [(Term.dotIdent "." `leaf) (Term.dotIdent "." `leaf)])] "]") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def s : T := .leaf.x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `s []) (Command.optDeclSig [] [(Term.typeSpec ":" `T)]) (Command.declValSimple ":=" (Term.dotIdent "." `leaf.x) (Termination.suffix [] []) []) []))"#,
    },
    // The boundary with the trailing projection: a `.` touching the term before it is
    // `Term.proj`; after whitespace it begins an argument.
    Accepted {
        source: "def p : Nat := (x).f",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `p []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `x ")") "." `f) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def q := f (x) .g",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `q []) (Command.optDeclSig [] []) (Command.declValSimple ":=" (Term.app `f [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `x ")") (Term.dotIdent "." `g)]) (Termination.suffix [] []) []) []))"#,
    },
];

/// `·`: `Term.cdot`, `unicodeSymbol "·" "." >> hygieneInfo` (`Lean/Parser/Term.lean:174`), spelled
/// `·` and `.`, alone and several, as an argument, under an ascription, nested, in a method
/// argument on a list literal, and unscoped (the parser takes it; the elaborator refuses it).
const CDOTS: &[Accepted] = &[
    Accepted {
        source: "def f : Nat → Nat := (· + 1)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.cdot "·" (hygieneInfo `[anonymous])) "+" (num "1")) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def f : Nat → Nat := (. + 1)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.cdot "." (hygieneInfo `[anonymous])) "+" (num "1")) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def f : Nat → Nat → Nat := (· + ·)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" (Term.arrow `Nat "→" `Nat)))]) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.cdot "·" (hygieneInfo `[anonymous])) "+" (Term.cdot "·" (hygieneInfo `[anonymous]))) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def f : Nat → Nat := (Nat.add · 2)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `Nat.add [(Term.cdot "·" (hygieneInfo `[anonymous])) (num "2")]) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def f := (· : Nat → Nat)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] []) (Command.declValSimple ":=" (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.cdot "·" (hygieneInfo `[anonymous])) ":" [(Term.arrow `Nat "→" `Nat)] ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def g (h : (Nat → Nat) → Nat → Nat) : Nat → Nat := (h (· + 1) ·)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `g []) (Command.optDeclSig [(Term.explicitBinder "(" [`h] [":" (Term.arrow (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.arrow `Nat "→" `Nat) ")") "→" (Term.arrow `Nat "→" `Nat))] [] ")")] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.app `h [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.cdot "·" (hygieneInfo `[anonymous])) "+" (num "1")) ")") (Term.cdot "·" (hygieneInfo `[anonymous]))]) ")") (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def m : List Nat := [1, 2, 3].map (· * 2)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `m []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `List [`Nat]))]) (Command.declValSimple ":=" (Term.app (Term.proj («term[_]» "[" [(num "1") "," (num "2") "," (num "3")] "]") "." `map) [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_*_» (Term.cdot "·" (hygieneInfo `[anonymous])) "*" (num "2")) ")")]) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def b : Nat := · + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `b []) (Command.optDeclSig [] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (Term.cdot "·" (hygieneInfo `[anonymous])) "+" (num "1")) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def x : Nat → Nat := fun x => (· + x) x",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `x []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» (Term.cdot "·" (hygieneInfo `[anonymous])) "+" `x) ")") [`x]))) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def f : Nat → Nat := (·)",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValSimple ":=" (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.cdot "·" (hygieneInfo `[anonymous])) ")") (Termination.suffix [] []) []) []))"#,
    },
];

/// Relations and existentials (bead `franken_lean-z8j.1.10`): `∃` is
/// `«term∃_,_»` over `Lean.explicitBinders` (`Init/NotationExtra.lean`), bare names with a
/// shared type or bracketed groups; `>`, `≥`, `≤`, `≠`, `!=`, `&&` and `||` are their
/// `Init/Notation.lean` / `Init/Core.lean` infixes, and an ASCII `>=` / `<=` builds the same
/// `«term_≥_»` / `«term_≤_»` node as its `unicode(…)` partner, keeping its own atom. A Nat
/// offset pattern `n + k` is `«term_+_»` in a match alternative, and a trailing `where` block
/// is `Term.whereDecls` of `letRecDecl`s in `declValSimple`'s last slot.
/// Captured as above, on 2026-10-06.
const RELATIONS_AND_EXISTENTIALS: &[Accepted] = &[
    Accepted {
        source: "theorem t : ∃ n : Nat, n = 1 := ⟨1, rfl⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t []) (Command.declSig [] (Term.typeSpec ":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" `Nat])) "," («term_=_» `n "=" (num "1"))))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "1") "," `rfl] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem t2 : ∃ x y : Nat, x = y := ⟨0, 0, rfl⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t2 []) (Command.declSig [] (Term.typeSpec ":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x) (Lean.binderIdent `y)] [":" `Nat])) "," («term_=_» `x "=" `y)))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0") "," (num "0") "," `rfl] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem t3 : ∃ (n : Nat) (m : Nat), n = m := ⟨0, 0, rfl⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `t3 []) (Command.declSig [] (Term.typeSpec ":" («term∃_,_» "∃" (Lean.explicitBinders [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `n)] ":" `Nat ")") (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" `Nat ")")]) "," («term_=_» `n "=" `m)))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0") "," (num "0") "," `rfl] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g : 3 > 2 := by decide",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g []) (Command.declSig [] (Term.typeSpec ":" («term_>_» (num "3") ">" (num "2")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g2 : 3 ≥ 2 := by decide",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g2 []) (Command.declSig [] (Term.typeSpec ":" («term_≥_» (num "3") "≥" (num "2")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem g3 : 3 >= 2 := by decide",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `g3 []) (Command.declSig [] (Term.typeSpec ":" («term_≥_» (num "3") ">=" (num "2")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem l : 2 ≤ 3 := by decide",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `l []) (Command.declSig [] (Term.typeSpec ":" («term_≤_» (num "2") "≤" (num "3")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem n : 2 ≠ 3 := by decide",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `n []) (Command.declSig [] (Term.typeSpec ":" («term_≠_» (num "2") "≠" (num "3")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem b : (2 != 3) = true := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `b []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_!=_» (num "2") "!=" (num "3")) ")") "=" `true))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem bo : (true && false || true) = true := rfl",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `bo []) (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_||_» («term_&&_» `true "&&" `false) "||" `true) ")") "=" `true))) (Command.declValSimple ":=" `rfl (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem le2 : 2 <= 3 := by decide",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `le2 []) (Command.declSig [] (Term.typeSpec ":" («term_≤_» (num "2") "<=" (num "3")))) (Command.declValSimple ":=" (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.decide "decide" (Tactic.optConfig []))]))) (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "theorem h : ∃ _ : Nat, True := ⟨0, trivial⟩",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.theorem "theorem" (Command.declId `h []) (Command.declSig [] (Term.typeSpec ":" («term∃_,_» "∃" (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent (Term.hole "_"))] [":" `Nat])) "," `True))) (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [(num "0") "," `trivial] "⟩") (Termination.suffix [] []) [])))"#,
    },
    Accepted {
        source: "def pred2 : Nat → Nat\n  | 0 => 0\n  | n + 1 => n",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `pred2 []) (Command.optDeclSig [] [(Term.typeSpec ":" (Term.arrow `Nat "→" `Nat))]) (Command.declValEqns (Term.matchAltsWhereDecls (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `n "+" (num "1"))]] "=>" `n)]) (Termination.suffix [] []) [])) []))"#,
    },
    Accepted {
        source: "def f (n : Nat) : Nat := match n with\n  | 0 => 0\n  | k + 2 => k\n  | _ => 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" (Term.match "match" [] [] [(Term.matchDiscr [] `n)] "with" (Term.matchAlts [(Term.matchAlt "|" [[(num "0")]] "=>" (num "0")) (Term.matchAlt "|" [[(«term_+_» `k "+" (num "2"))]] "=>" `k) (Term.matchAlt "|" [[(Term.hole "_")]] "=>" (num "1"))])) (Termination.suffix [] []) []) []))"#,
    },
    Accepted {
        source: "def f (n : Nat) : Nat := g n + 1\nwhere g (m : Nat) : Nat := m * 2",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (Term.app `g [`n]) "+" (num "1")) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `g) [(Term.explicitBinder "(" [`m] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" («term_*_» `m "*" (num "2")))) (Termination.suffix [] []))] [])]) []))"#,
    },
    Accepted {
        source: "def f (n : Nat) : Nat := g n + h n\nwhere\n  g (m : Nat) : Nat := m * 2\n  h (m : Nat) : Nat := g m + 1",
        tree: r#"(Command.declaration (Command.declModifiers [] [] [] [] [] [] []) (Command.definition "def" (Command.declId `f []) (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)]) (Command.declValSimple ":=" («term_+_» (Term.app `g [`n]) "+" (Term.app `h [`n])) (Termination.suffix [] []) [(Term.whereDecls "where" [(Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `g) [(Term.explicitBinder "(" [`m] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" («term_*_» `m "*" (num "2")))) (Termination.suffix [] [])) [] (Term.letRecDecl [] [] (Term.letDecl (Term.letIdDecl (Term.letId `h) [(Term.explicitBinder "(" [`m] [":" `Nat] [] ")")] [(Term.typeSpec ":" `Nat)] ":=" («term_+_» (Term.app `g [`m]) "+" (num "1")))) (Termination.suffix [] []))] [])]) []))"#,
    },
];

/// Malformed `⟨…⟩`, refused at the pin's token. Captured as above (the pin's columns count
/// code points; `at` is the byte offset in `source`).
const ANONYMOUS_CONSTRUCTOR_REFUSALS: &[Refused] = &[
    Refused {
        source: "def p : Point := ⟨1,, 2⟩",
        message: "4:20: error: unexpected token ','; expected '⟩'",
        at: 22,
    },
    Refused {
        source: "def p : Point := ⟨,⟩",
        message: "4:18: error: unexpected token ','; expected '⟩'",
        at: 20,
    },
];

/// Modifiers out of the pin's order: the pin stops at the first one it cannot place.
const MODIFIER_REFUSALS: &[Refused] = &[
    Refused {
        source: "protected private def j : Nat := 7",
        message: "1:9: error: unexpected token 'private'; expected 'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'structure' or 'theorem'",
        at: 10,
    },
    Refused {
        source: "unsafe protected def k : Nat := 8",
        message: "1:6: error: unexpected token 'protected'; expected 'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'structure' or 'theorem'",
        at: 7,
    },
];

/// FrankenLean's tree in the pin's `Syntax.toString` vocabulary, on one line.
fn render(syntax: &Syntax, out: &mut String) {
    match syntax {
        Syntax::Missing => out.push_str("<missing>"),
        Syntax::Atom { val, .. } => out.push_str(&format!("{:?}", val.as_str())),
        // `Name.toString` spells the anonymous name `[anonymous]` (`hygieneInfo`'s identifier).
        Syntax::Ident { val, .. } if val.is_anonymous() => out.push_str("`[anonymous]"),
        Syntax::Ident { val, .. } => {
            out.push('`');
            push_name(out, &name_parts(val));
        }
        Syntax::Node { kind, args, .. } => {
            let display = kind.to_display_string();
            if display == "null" {
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

/// A name's own components, not its display split at dots: a component may hold dots
/// (`Std.«term_...<_»`).
fn name_parts(name: &fln_core::name::Name) -> Vec<String> {
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

/// `Name.toString` escapes each component on its own: `Tactic.«tactic_<;>_»`, `` `«term_<&&>_»``.
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

fn rendered(source: &str) -> Result<String, DefinitionParseError> {
    let parsed = parse_definition(source.as_bytes())?;
    let mut out = String::new();
    render(parsed.syntax(), &mut out);
    Ok(out)
}

#[test]
fn declaration_modifiers_produce_the_pins_trees() {
    for row in MODIFIERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn inline_attributes_produce_the_pins_trees() {
    for row in ATTRIBUTES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn conditionals_produce_the_pins_trees() {
    for row in CONDITIONALS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn infixes_and_untyped_binders_produce_the_pins_trees() {
    for row in INFIXES_AND_UNTYPED_BINDERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn anonymous_instances_produce_the_pins_trees() {
    for row in ANONYMOUS_INSTANCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn anonymous_constructors_produce_the_pins_trees() {
    for row in ANONYMOUS_CONSTRUCTORS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn anonymous_constructor_patterns_produce_the_pins_trees() {
    for row in ANONYMOUS_CONSTRUCTOR_PATTERNS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn substitutions_produce_the_pins_trees() {
    for row in SUBSTITUTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn pipe_right_produces_the_pins_trees() {
    for row in PIPE_RIGHT {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn infer_instance_as_produces_the_pins_trees() {
    for row in INFER_INSTANCE_AS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn opaques_produce_the_pins_trees() {
    for row in OPAQUES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn abbreviations_produce_the_pins_trees() {
    for row in ABBREVIATIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn locals_in_alternatives_produce_the_pins_trees() {
    for row in LOCALS_IN_ALTERNATIVES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn declaration_where_produces_the_pins_trees() {
    for row in DECLARATION_WHERE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn binder_predicates_produce_the_pins_trees() {
    for row in BINDER_PREDICATES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn binder_defaults_produce_the_pins_trees() {
    for row in BINDER_DEFAULTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn hole_binders_produce_the_pins_trees() {
    for row in HOLE_BINDERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn local_instances_borrows_and_ellipses_produce_the_pins_trees() {
    for row in LOCAL_INSTANCES_BORROWS_ELLIPSES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn more_tactics_produce_the_pins_trees() {
    for row in MORE_TACTICS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn rcases_produces_the_pins_trees() {
    for row in RCASES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn scope_in_commands_produce_the_pins_trees() {
    for row in SCOPE_IN_COMMANDS {
        let tree = fln_parse::command_scope::trees::command_tree(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(&tree, &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn scope_commands_produce_the_pins_trees() {
    for row in SCOPE_COMMANDS {
        let tree = fln_parse::command_scope::trees::command_tree(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(&tree, &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
    }
    for source in [
        "namespace",
        "namespace A B",
        "end A B",
        "open",
        "open Nat (",
        "open Nat hiding",
        "open Nat renaming add",
        "open Nat renaming add → plus,",
        "set_option pp.all",
        "set_option pp.all true in",
        // An `in` with no command after it is refused, not read past the last token.
        "open A in",
        "open Nat (succ) in",
        "open Nat hiding add in",
        "set_option pp.all foo",
        "section A B",
    ] {
        assert_eq!(
            fln_parse::command_scope::trees::tree(source.as_bytes())
                .ok()
                .flatten(),
            None,
            "{source}"
        );
    }
}

#[test]
fn attribute_commands_produce_the_pins_trees() {
    for row in ATTRIBUTE_COMMANDS {
        let tree = fln_parse::command_scope::trees::command_tree(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(&tree, &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
    }
    for source in [
        "attribute",
        "attribute [simp]",
        "attribute [simp] t1 2",
        "attribute [-] t1",
        "attribute [simp,] t1",
    ] {
        assert_eq!(
            fln_parse::command_scope::trees::tree(source.as_bytes())
                .ok()
                .flatten(),
            None,
            "{source}"
        );
    }
}

#[test]
fn headed_sections_produce_the_pins_trees() {
    for row in HEADED_SECTIONS {
        let parsed = fln_parse::parse_source_command(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(parsed.syntax(), &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(row.source.as_bytes()),
            "{}",
            row.source
        );
    }
}

#[test]
fn syntax_declarations_produce_the_pins_trees() {
    for row in SYNTAX_DECLARATIONS.iter().chain(NOTATION_DECLARATIONS) {
        let parsed = fln_parse::parse_source_command(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(parsed.syntax(), &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(row.source.as_bytes()),
            "{}",
            row.source
        );
    }
    for source in [
        "syntax \"x\"",
        "syntax : term",
        "syntax \"x\" (term : term",
        "syntax \"x\" term:foo : term",
        "syntax n :=",
        "scoped syntax n := \"x\"",
        "private syntax \"x\" : term",
        "syntax \"x\" sepBy(term) : term",
        "infixl \" +++ \" => f",
        "infixl:65 a \" +++ \" => f",
        "notation \"x\" =>",
        "notation \"x\" f",
        "recommended_spelling \"a\" for \"b\" in [x,]",
        "private notation \"x\" => f",
    ] {
        assert!(
            fln_parse::parse_source_command(source.as_bytes()).is_err(),
            "{source}"
        );
    }
}

#[test]
fn grind_patterns_produce_the_pins_trees() {
    for row in GRIND_PATTERNS {
        let parsed = fln_parse::parse_source_command(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(parsed.syntax(), &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
        assert_eq!(
            parsed.reconstruct_normalized().as_deref(),
            Some(row.source.as_bytes()),
            "{}",
            row.source
        );
    }
}

#[test]
fn bind_list_relations_and_prefixes_produce_the_pins_trees() {
    for row in BIND_LIST_RELATIONS_AND_PREFIXES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn instance_pipes_bool_conditionals_and_proved_indices_produce_the_pins_trees() {
    for row in INSTANCE_PIPES_BOOL_CONDITIONALS_AND_PROVED_INDICES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn pipeline_projections_produce_the_pins_trees() {
    for row in PIPELINE_PROJECTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn defaults_flags_and_pattern_binders_produce_the_pins_trees() {
    for row in DEFAULTS_FLAGS_AND_PATTERN_BINDERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn sums_scalars_and_more_tactics_produce_the_pins_trees() {
    for row in SUMS_SCALARS_AND_MORE_TACTICS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn matches_in_types_and_field_equations_produce_the_pins_trees() {
    for row in MATCHES_IN_TYPES_AND_FIELD_EQUATIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tactic_matches_and_ascribed_proofs_produce_the_pins_trees() {
    for row in TACTIC_MATCHES_AND_ASCRIBED_PROOFS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn functional_induction_produces_the_pins_trees() {
    for row in FUNCTIONAL_INDUCTION {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn bounded_ranges_produce_the_pins_trees() {
    for row in BOUNDED_RANGES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn ascii_focus_and_inverse_produce_the_pins_trees() {
    for row in ASCII_FOCUS_AND_INVERSE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn line_separated_fields_produce_the_pins_trees() {
    for row in LINE_SEPARATED_FIELDS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn termination_clauses_produce_the_pins_trees() {
    for row in TERMINATION_CLAUSES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tuple_patterns_produce_the_pins_trees() {
    for row in TUPLE_PATTERNS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn scoped_instances_produce_the_pins_trees() {
    for row in SCOPED_INSTANCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn vectors_and_hole_locals_produce_the_pins_trees() {
    for row in VECTORS_AND_HOLE_LOCALS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tactic_conditionals_produce_the_pins_trees() {
    for row in TACTIC_CONDITIONALS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn simp_order_xor_and_tactics_produce_the_pins_trees() {
    for row in SIMP_ORDER_XOR_AND_TACTICS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn generalize_arguments_produce_the_pins_trees() {
    for row in GENERALIZE_ARGUMENTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn first_and_try_produce_the_pins_trees() {
    for row in FIRST_AND_TRY {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn constructor_docs_and_repeat_produce_the_pins_trees() {
    for row in CONSTRUCTOR_DOCS_AND_REPEAT {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn fields_closed_left_of_them_produce_the_pins_trees() {
    for row in FIELDS_CLOSED_LEFT_OF_THEM {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn mixed_associativity_produces_the_pins_trees() {
    for row in MIXED_ASSOCIATIVITY {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn let_rec_and_solve_by_elim_produce_the_pins_trees() {
    for row in LET_REC_AND_SOLVE_BY_ELIM {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn conv_blocks_produce_the_pins_trees() {
    for row in CONV_BLOCKS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn leaf_tactics_two_produce_the_pins_trees() {
    for row in LEAF_TACTICS_TWO {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn conv_focus_apply_simp_produce_the_pins_trees() {
    for row in CONV_FOCUS_APPLY_SIMP {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn word_priorities_produce_the_pins_trees() {
    for row in WORD_PRIORITIES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn index_proof_projections_produce_the_pins_trees() {
    for row in INDEX_PROOF_PROJECTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn do_local_functions_produce_the_pins_trees() {
    for row in DO_LOCAL_FUNCTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn nested_by_sequences_produce_the_pins_trees() {
    for row in NESTED_BY_SEQUENCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn else_branch_sequences_produce_the_pins_trees() {
    for row in ELSE_BRANCH_SEQUENCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn sequencing_and_heq_produce_the_pins_trees() {
    for row in SEQUENCING_AND_HEQ {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn named_patterns_produce_the_pins_trees() {
    for row in NAMED_PATTERNS {
        let parsed = fln_parse::parse_source_command(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(parsed.syntax(), &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn ascribed_patterns_produce_the_pins_trees() {
    for row in ASCRIBED_PATTERNS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn structure_constructors_and_private_fields_produce_the_pins_trees() {
    for row in STRUCTURE_CONSTRUCTORS_AND_PRIVATE_FIELDS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn protected_fields_produce_the_pins_trees() {
    for row in PROTECTED_FIELDS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn empty_matches_produce_the_pins_trees() {
    for row in EMPTY_MATCHES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn deriving_commands_produce_the_pins_trees() {
    for row in DERIVING_COMMANDS {
        let parsed = fln_parse::parse_source_command(row.source.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        let mut ours = String::new();
        render(parsed.syntax(), &mut ours);
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn chains_across_lines_produce_the_pins_trees() {
    for row in CHAINS_ACROSS_LINES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn with_tactics_and_wildcard_alternatives_produce_the_pins_trees() {
    for row in WITH_TACTICS_AND_WILDCARD_ALTERNATIVES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn where_docs_and_attributes_produce_the_pins_trees() {
    for row in WHERE_DOCS_AND_ATTRIBUTES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn let_rec_attributes_produce_the_pins_trees() {
    for row in LET_REC_ATTRIBUTES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn orelse_exists_and_done_produce_the_pins_trees() {
    for row in ORELSE_EXISTS_AND_DONE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn chained_sequences_produce_the_pins_trees() {
    for row in CHAINED_SEQUENCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn elimination_targets_produce_the_pins_trees() {
    for row in ELIMINATION_TARGETS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn using_terms_produce_the_pins_trees() {
    for row in USING_TERMS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn case_bodies_produce_the_pins_trees() {
    for row in CASE_BODIES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn conv_chains_produce_the_pins_trees() {
    for row in CONV_CHAINS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn leaf_tactics_three_produce_the_pins_trees() {
    for row in LEAF_TACTICS_THREE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn bare_binders_and_ellipses_produce_the_pins_trees() {
    for row in BARE_BINDERS_AND_ELLIPSES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn arrow_positions_produce_the_pins_trees() {
    for row in ARROW_POSITIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tactic_opens_produce_the_pins_trees() {
    for row in TACTIC_OPENS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn by_owned_chains_produce_the_pins_trees() {
    for row in BY_OWNED_CHAINS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn range_positions_produce_the_pins_trees() {
    for row in RANGE_POSITIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn term_binder_defaults_produce_the_pins_trees() {
    for row in TERM_BINDER_DEFAULTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn structure_modifiers_produce_the_pins_trees() {
    for row in STRUCTURE_MODIFIERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn show_after_prefix_produce_the_pins_trees() {
    for row in SHOW_AFTER_PREFIX {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn cdot_heads_produce_the_pins_trees() {
    for row in CDOT_HEADS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn field_tactic_defaults_produce_the_pins_trees() {
    for row in FIELD_TACTIC_DEFAULTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn calculations_produce_the_pins_trees() {
    for row in CALCULATIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn shared_alternatives_produce_the_pins_trees() {
    for row in SHARED_ALTERNATIVES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn rcases_names_and_coe_produce_the_pins_trees() {
    for row in RCASES_NAMES_AND_COE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn mutable_do_variables_produce_the_pins_trees() {
    for row in MUTABLE_DO_VARIABLES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn range_arguments_produce_the_pins_trees() {
    for row in RANGE_ARGUMENTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn constructor_doc_layouts_produce_the_pins_trees() {
    for row in CONSTRUCTOR_DOC_LAYOUTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn do_else_if_produce_the_pins_trees() {
    for row in DO_ELSE_IF {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn empty_where_instances_produce_the_pins_trees() {
    for row in EMPTY_WHERE_INSTANCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn local_equations_produce_the_pins_trees() {
    for row in LOCAL_EQUATIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn term_if_let_produce_the_pins_trees() {
    for row in TERM_IF_LET {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn with_only_eliminations_produce_the_pins_trees() {
    for row in WITH_ONLY_ELIMINATIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn term_pattern_lets_produce_the_pins_trees() {
    for row in TERM_PATTERN_LETS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn branch_pattern_lets_and_bare_ascriptions_produce_the_pins_trees() {
    for row in BRANCH_PATTERN_LETS_AND_BARE_ASCRIPTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn intro_patterns_and_local_binders_produce_the_pins_trees() {
    for row in INTRO_PATTERNS_AND_LOCAL_BINDERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn let_rec_tactics_and_bracketed_sequences_produce_the_pins_trees() {
    for row in LET_REC_TACTICS_AND_BRACKETED_SEQUENCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn for_patterns_and_do_let_rec_produce_the_pins_trees() {
    for row in FOR_PATTERNS_AND_DO_LET_REC {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn own_line_alternative_bodies_produce_the_pins_trees() {
    for row in OWN_LINE_ALTERNATIVE_BODIES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn comma_targets_and_inline_shared_rows_produce_the_pins_trees() {
    for row in COMMA_TARGETS_AND_INLINE_SHARED_ROWS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn list_pattern_tuples_produce_the_pins_trees() {
    for row in LIST_PATTERN_TUPLES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn proof_pipes_in_terms_produce_the_pins_trees() {
    for row in PROOF_PIPES_IN_TERMS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn binder_fields_produce_the_pins_trees() {
    for row in BINDER_FIELDS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn change_at_anonymous_let_and_hole_conditions_produce_the_pins_trees() {
    for row in CHANGE_AT_ANONYMOUS_LET_AND_HOLE_CONDITIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn term_opens_produce_the_pins_trees() {
    for row in TERM_OPENS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn intro_match_alternatives_match_the_pin() {
    for row in INTRO_MATCH_ALTERNATIVES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn conv_keywords_unfold_and_intro_match_the_pin() {
    for row in CONV_KEYWORDS_UNFOLD_AND_INTRO {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn let_rec_equations_match_the_pin() {
    for row in LET_REC_EQUATIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn raw_nat_literals_and_anonymous_lets_match_the_pin() {
    for row in RAW_NAT_LITERALS_AND_ANONYMOUS_LETS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn where_attributes_default_overrides_and_finally_match_the_pin() {
    for row in WHERE_ATTRIBUTES_DEFAULT_OVERRIDES_AND_FINALLY {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn method_specs_simp_attributes_match_the_pin() {
    for row in METHOD_SPECS_SIMP_ATTRIBUTES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn simp_rule_commas_and_show_binders_match_the_pin() {
    for row in SIMP_RULE_COMMAS_AND_SHOW_BINDERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn constructor_names_and_modifiers_match_the_pin() {
    for row in CONSTRUCTOR_NAMES_AND_MODIFIERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn hole_alternatives_and_constructor_proofs_match_the_pin() {
    for row in HOLE_ALTERNATIVES_AND_CONSTRUCTOR_PROOFS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn grind_parameters_match_the_pin() {
    for row in GRIND_PARAMETERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn antiquotation_heads_match_the_pin() {
    for row in ANTIQUOTATION_HEADS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn quotation_conditionals_match_the_pin() {
    for row in QUOTATION_CONDITIONALS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn field_equations_and_binder_bodies_match_the_pin() {
    for row in FIELD_EQUATIONS_AND_BINDER_BODIES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn keyword_field_projections_match_the_pin() {
    for row in KEYWORD_FIELD_PROJECTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tactic_if_branch_chains_match_the_pin() {
    for row in TACTIC_IF_BRANCH_CHAINS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn simp_dischargers_match_the_pin() {
    for row in SIMP_DISCHARGERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn shared_match_alternatives_match_the_pin() {
    for row in SHARED_MATCH_ALTERNATIVES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn equivalences_produce_the_pins_trees() {
    for row in EQUIVALENCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn named_patterns_as_constructor_arguments_produce_the_pins_trees() {
    for row in NAMED_PATTERN_ARGUMENTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn if_and_match_after_an_arrow_are_do_elements() {
    for row in ARROW_DO_ELEMENTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn injection_names_may_be_holes() {
    for row in INJECTION_HOLES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn unbounded_ranges_produce_the_pins_trees() {
    for row in UNBOUNDED_RANGES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn do_level_have_produces_the_pins_trees() {
    for row in DO_HAVE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn where_termination_hints_produce_the_pins_trees() {
    for row in WHERE_TERMINATION {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn let_rec_termination_hints_produce_the_pins_trees() {
    for row in LET_REC_TERMINATION {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn let_rec_decreasing_by_owns_its_semicolons() {
    for row in LET_REC_DECREASING_BLOCK {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn a_hint_at_the_tactic_column_keeps_a_trailing_separator() {
    for row in TRAILING_TACTIC_SEPARATOR {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn matches_produces_the_pins_trees() {
    for row in MATCHES_NOTATION {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn attributed_instances_produce_the_pins_trees() {
    for row in ATTRIBUTED_INSTANCES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn the_coercion_arrow_produces_the_pins_trees() {
    for row in COERCION_ARROW {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn dollar_produces_the_pins_trees() {
    for row in DOLLAR_PIPELINE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn let_rec_termination_before_a_semicolon() {
    for row in LET_REC_SEMICOLON_TERMINATION {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn calc_step_positions_produce_the_pins_trees() {
    for row in CALC_STEP_POSITIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn definition_deriving_produces_the_pins_trees() {
    for row in DEFINITION_DERIVING {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn do_while_produces_the_pins_trees() {
    for row in DO_WHILE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn inductive_modifiers_produce_the_pins_trees() {
    for row in INDUCTIVE_MODIFIERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn pattern_reassignment_produces_the_pins_trees() {
    for row in PATTERN_REASSIGNMENT {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tactic_pattern_bindings_produce_the_pins_trees() {
    for row in TACTIC_PATTERN_BINDINGS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn a_projection_after_a_named_argument_projects_the_application() {
    for row in NAMED_ARGUMENT_PROJECTION {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn a_by_block_ends_at_the_next_alternative() {
    for row in BY_BLOCK_ENDS_AT_AN_ALTERNATIVE {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn suffices_cases_and_goals_produce_the_pins_trees() {
    for row in SUFFICES_CASES_AND_GOALS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn subtypes_produce_the_pins_trees() {
    for row in SUBTYPES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn nested_actions_produce_the_pins_trees() {
    for row in NESTED_ACTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn arrays_produce_the_pins_trees() {
    for row in ARRAYS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tuples_produce_the_pins_trees() {
    for row in TUPLES {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn indexing_produces_the_pins_trees() {
    for row in INDEXING {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tactic_forms_produce_the_pins_trees() {
    for row in TACTIC_FORMS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn tactic_blocks_produce_the_pins_trees() {
    for row in TACTIC_BLOCKS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn nested_proofs_produce_the_pins_trees() {
    for row in NESTED_PROOFS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn numeric_projections_produce_the_pins_trees() {
    for row in NUMERIC_PROJECTIONS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn dotted_identifiers_produce_the_pins_trees() {
    for row in DOTTED_IDENTIFIERS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn relations_and_existentials_produce_the_pins_trees() {
    for row in RELATIONS_AND_EXISTENTIALS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}

#[test]
fn cdots_produce_the_pins_trees() {
    for row in CDOTS {
        let ours = rendered(row.source).unwrap_or_else(|error| panic!("{}: {error:?}", row.source));
        assert_eq!(ours, row.tree, "{}", row.source);
    }
}
#[test]
fn modifiers_out_of_order_are_refused_at_the_pins_token() {
    refusals_agree(MODIFIER_REFUSALS);
}

#[test]
fn malformed_anonymous_constructors_are_refused_at_the_pins_token() {
    refusals_agree(ANONYMOUS_CONSTRUCTOR_REFUSALS);
}

fn refusals_agree(rows: &[Refused]) {
    for row in rows {
        // The pin reports the end of the preceding token; the token it names comes next.
        let named = row
            .message
            .split('\'')
            .nth(1)
            .expect("the message names a token");
        assert_eq!(
            &row.source[row.at..row.at + named.len()],
            named,
            "{}",
            row.source
        );
        match parse_definition(row.source.as_bytes()) {
            Err(NatDefinitionParseError::OutsideSeedGrammar { at, .. }) => {
                assert_eq!(at, BytePos(row.at), "{}", row.source);
            }
            other => panic!(
                "{}: the pin refuses ({}), got {other:?}",
                row.source, row.message
            ),
        }
    }
}

/// The renderer is not vacuous: a tree with a modifier moved to another slot renders
/// differently from the pin's row, so the fixture can tell the slots apart.
#[test]
fn a_misplaced_modifier_does_not_render_as_the_pins_tree() {
    let pin = MODIFIERS[0].tree;
    let moved = pin.replacen(
        r#"[] [] [] [(Command.protected "protected")] [] [] []"#,
        r#"[] [] [(Command.protected "protected")] [] [] [] []"#,
        1,
    );
    assert_ne!(moved, pin);
    assert_ne!(rendered(MODIFIERS[0].source).unwrap(), moved);
}
