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
            let shown = display.strip_prefix("Lean.Parser.").unwrap_or(&display);
            out.push('(');
            // `Name.toString` escapes each component on its own: `Tactic.«tactic_<;>_»`.
            for (i, part) in shown.split('.').enumerate() {
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
