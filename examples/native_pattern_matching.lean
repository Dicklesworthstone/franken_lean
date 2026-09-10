inductive Maybe (A : Type) where
  | none
  | some (value : A)

def get (item : Maybe Nat) : Nat := match item with
  | .none => 0
  | .some value => value

theorem payload_ok : get (Maybe.some 23) = 23 := by rfl
theorem none_ok : get Maybe.none = 0 := by rfl

inductive Tree where
  | leaf (value : Nat)
  | fork (left right : Tree)

def leftBranch (tree : Tree) : Tree := match tree with
  | .leaf value => Tree.leaf value
  | .fork left right => left

theorem branch_ok : leftBranch (Tree.fork (Tree.leaf 7) (Tree.leaf 9)) = Tree.leaf 7 := by rfl

def predecessor (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ previous => previous

theorem zero_ok : predecessor 0 = 0 := by rfl
theorem large_ok : predecessor 340282366920938463463374607431768211456 = 340282366920938463463374607431768211455 := by rfl

structure Package where
  carrier : Type
  value : carrier

def unpack (package : Package) : package.carrier := match package with
  | Package.mk carrier value => value

def packed : Package := { carrier := Nat, value := 17 }
theorem dependent_ok : unpack packed = 17 := by rfl

theorem bool_refl (b : Bool) : b = b := match b with
  | true => by rfl
  | false => by rfl
