@[export plug_add_five]
def addFive (n : Nat) : Nat := n + 5

@[export plug_greet]
def greet (s : String) : String := s ++ " from the plugin"
