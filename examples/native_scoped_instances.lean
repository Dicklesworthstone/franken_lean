class Selection where
  value : Nat
def selected [Selection] : Nat := Selection.value
def fallbackSelection : Selection := Selection.mk 1
attribute [instance] fallbackSelection

namespace Alternative
  def dictionary : Selection := Selection.mk 7
  attribute [scoped instance] dictionary
  theorem activeHere : selected = 7 := by rfl
end Alternative

theorem dormantOutside : selected = 1 := by rfl
section
  open scoped Alternative
  theorem explicitlyOpened : selected = 7 := by rfl
end

theorem restoredOutside : selected = 1 := by rfl
open Alternative
theorem ordinaryOpenAlsoActivates : selected = 7 := by rfl
