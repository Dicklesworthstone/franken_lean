prelude
universe u
class Inhabited (α : Sort u) where
  default : α
def default {α : Sort u} [inst : Inhabited α] : α := Inhabited.default
inductive Flag where
  | stop
  | again
partial def keep {α : Type} (x : α) (flag : Flag) : α :=
  match flag with
  | Flag.stop => x
  | Flag.again => keep x Flag.stop
partial def rotate (flag : Flag) : Flag :=
  match flag with
  | Flag.stop => Flag.again
  | Flag.again => rotate Flag.stop
