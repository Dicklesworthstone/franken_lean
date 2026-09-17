-- Typed lambdas infer their own function signatures.
def typedId := fun (x : Nat) => x
theorem typedId_ok : typedId 19 = 19 := by rfl

-- The expected type inserts an implicit universe-polymorphic binder.
def polyId : {A : Sort _} -> A -> A := fun x => x
def low : Nat := polyId 7
def high : Type := polyId Nat
theorem low_ok : low = 7 := by rfl

-- Later domains and results can depend on earlier binders.
def dependentApply (A : Type) (P : A -> Type)
    (f : (x : A) -> P x) (x : A) : P x := f x

def choose : {A : Type} -> {B : Type} -> A -> B -> A := fun x y => x
theorem choose_ok : choose 7 true = 7 := by rfl

-- Inserted instance binders participate in ordinary local instance search.
class Item (A : Type) where
  value : A

def get : {A : Type} -> [d : Item A] -> Nat -> A := fun (_ : Nat) => Item.value
instance natItem : Item Nat := { value := 7 }
theorem get_ok : get 0 = 7 := by rfl
