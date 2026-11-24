prelude
axiom A : Type
axiom p : A -> Prop
axiom trigger : A -> A
axiom other : A -> A
theorem rule (x : A) (h : p x) : p x := h
grind_pattern rule => trigger x
grind_pattern rule => other x
