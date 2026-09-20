-- Global attributes on already checked dictionaries, including priority changes.
namespace NativeInstanceAttributes

def seven : Inhabited Nat := Inhabited.mk 7
def nine : Inhabited Nat := Inhabited.mk 9

attribute [instance 3000] seven
theorem selectedSeven : default = 7 := by rfl

attribute [instance 4000] nine
theorem selectedNine : default = 9 := by rfl

-- Updating the earlier registration does not make it the newer equal-priority peer.
attribute [instance 4000] seven
theorem tied : default = 9 := by rfl

attribute [instance 5000] seven
theorem raised : default = 7 := by rfl

attribute [instance 100] seven
theorem lowered : default = 9 := by rfl

end NativeInstanceAttributes
