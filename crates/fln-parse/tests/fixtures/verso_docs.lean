set_option doc.verso true

/--
A first line with `code` and {name}`Nat`.
A continuation line.

* A bullet with {name}`Nat.succ`.
* Another bullet
  continued here.

A closing paragraph with *bold*, _emph_ and **strong**.
-/
def a1 : Nat := 1

/-- Emphasis inside a double-asterisk bold: **_both_**. -/
def a1' : Nat := 1

/-- Escapes \{ and \* here, and `` ` `` code. -/
def a2 : Nat := 2

/-- {name (full := Nat.succ)}`succ`, {lean}`1 + 1`, {given -show}`n : Nat` and {lit}[text]. -/
def a3 : Nat := 3

/-!
# A Header

Text under it.
-/

/--
Code block:
```lean
def x := 1
```

1. First
2. Second

> Quoted

A [link](https://lean-lang.org), an ![image](pic.png), $`x` and $$`y`.

{tactic_docs}
-/
def a4 : Nat := 4

structure S where
  /--
  Indented two
  lines.
  -/
  y : Nat

/-- An unclosed [link -/
def a5 : Nat := 5

section
set_option doc.verso false

/-- Plain {name}`Nat` again. -/
def a6 : Nat := 6

set_option doc.verso true in
/-- Still plain after `set_option … in`, {name}`Nat`. -/
def a7 : Nat := 7
end

/-- After the section, {name}`Nat`. -/
def a8 : Nat := 8
