inductive Sequence (A : Type) where
  | nil
  | cons (head : A) (tail : Sequence A)

def length {A : Type} (xs : Sequence A) : Nat := match xs with
  | .nil => 0
  | .cons x tail => length tail + 1

def map {A B : Type} (f : A -> B) (xs : Sequence A) : Sequence B := match xs with
  | .nil => Sequence.nil
  | .cons x tail => Sequence.cons (f x) (map f tail)

def append {A : Type} (xs : Sequence A) (ys : Sequence A) : Sequence A := match xs with
  | .nil => ys
  | .cons x tail => Sequence.cons x (append tail ys)

theorem map_identity {A : Type} (xs : Sequence A) : map (fun x => x) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [map, ih]

theorem map_composition {A B C : Type} (f : A -> B) (g : B -> C) (xs : Sequence A) :
    map g (map f xs) = map (fun x => g (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [map, ih]

theorem append_right_nil {A : Type} (xs : Sequence A) : append xs Sequence.nil = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [append, ih]

theorem append_associative {A : Type} (xs ys zs : Sequence A) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [append, ih]

def numbers : Sequence Nat := append (Sequence.cons 7 Sequence.nil) (Sequence.cons 9 Sequence.nil)
theorem length_ok : length numbers = 2 := by rfl

theorem append_computes : numbers = Sequence.cons 7 (Sequence.cons 9 Sequence.nil) := by rfl

inductive Tree (A : Type) where
  | leaf (value : A)
  | fork (left right : Tree A)

def mirror {A : Type} (tree : Tree A) : Tree A := match tree with
  | .leaf x => Tree.leaf x
  | .fork left right => Tree.fork (mirror right) (mirror left)

theorem mirror_involutive {A : Type} (tree : Tree A) : mirror (mirror tree) = tree := by
  induction tree with
  | leaf x => rfl
  | fork left right hl hr => simp only [mirror, hl, hr]
