import Lib

def wrapBox.{u} {α : Sort u} (x : α) : α := boxIdentity x

def keepFirst.{u} {α : Sort u} (x y : α) : α := boxConst x y
