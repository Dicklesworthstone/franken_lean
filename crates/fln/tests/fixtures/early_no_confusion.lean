prelude

universe u v

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1}
    (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

inductive Bool : Type where
  | false : Bool
  | true : Bool

inductive Empty : Type
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PEmpty : Sort u
