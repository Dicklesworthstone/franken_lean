inductive Seq (A : Type) where
  | nil
  | cons (head : A) (tail : Seq A)

def length {A : Type} (xs : Seq A) : Nat := match xs with
  | .nil => 0
  | .cons x tail => length tail + 1

def map {A B : Type} (f : A -> B) (xs : Seq A) : Seq B := match xs with
  | .nil => Seq.nil
  | .cons x tail => Seq.cons (f x) (map f tail)

def append {A : Type} (xs : Seq A) (ys : Seq A) : Seq A := match xs with
  | .nil => ys
  | .cons x tail => Seq.cons x (append tail ys)

theorem map_identity {A : Type} (xs : Seq A) : map (fun x => x) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [map, ih]

theorem map_composition {A B C : Type} (f : A -> B) (g : B -> C) (xs : Seq A) :
    map g (map f xs) = map (fun x => g (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [map, ih]

theorem append_right_nil {A : Type} (xs : Seq A) : append xs Seq.nil = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [append, ih]

theorem append_associative {A : Type} (xs ys zs : Seq A) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [append, ih]

def numbers : Seq Nat := append (Seq.cons 7 Seq.nil) (Seq.cons 9 Seq.nil)
theorem length_ok : length numbers = 2 := by rfl

theorem append_computes : numbers = Seq.cons 7 (Seq.cons 9 Seq.nil) := by rfl

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
