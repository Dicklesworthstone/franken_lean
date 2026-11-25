inductive NatBox where
  | mk : NatBox

def boxIdentity.{u} {α : Sort u} (x : α) : α := x

def boxConst.{u} {α : Sort u} (x : α) (_y : α) : α := x
