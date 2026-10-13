prelude
import Lib
def after : Flag := rotate Flag.stop
def retained {α : Type} (x : α) : α := keep x Flag.again
