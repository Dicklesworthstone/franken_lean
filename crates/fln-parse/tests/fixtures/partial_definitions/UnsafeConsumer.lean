prelude
import Lib
def leak {α : Type} (x : α) : α := keep._unsafe_rec x Flag.again
