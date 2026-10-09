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
        Syntax::Ident { val, .. } => {
            out.push('`');
            out.push_str(&val.to_display_string());
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
            // The kind's own components, not its display split at dots: a component may hold
            // dots (`Std.«term_...<_»`).
            let mut parts = Vec::new();
            let mut cursor = kind.clone();
            while !cursor.is_anonymous() {
                parts.push(match cursor.leaf_view() {
                    fln_core::name::LeafView::Str(part) => part.to_owned(),
                    fln_core::name::LeafView::Num(part) => part.to_string(),
                    fln_core::name::LeafView::Anonymous => String::new(),
                });
                cursor = cursor.parent();
            }
            parts.reverse();
            if parts.len() > 2 && parts[0] == "Lean" && parts[1] == "Parser" {
                parts.drain(..2);
            }
            out.push('(');
            // `Name.toString` escapes each component on its own: `Tactic.«tactic_<;>_»`.
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
            for arg in args {
                out.push(' ');
                render(arg, out);
            }
            out.push(')');
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
