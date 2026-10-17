-- These namespaces have the same printed dot sequence but different Name components.
namespace «A.B»
def leaf : Nat := 3
def step1 : Nat := Nat.add leaf leaf
def step2 : Nat := Nat.add step1 step1
def step3 : Nat := Nat.add step2 step2
def step4 : Nat := Nat.add step3 step3
def step5 : Nat := Nat.add step4 step4
def step6 : Nat := Nat.add step5 step5
def step7 : Nat := Nat.add step6 step6
def step8 : Nat := Nat.add step7 step7
def step9 : Nat := Nat.add step8 step8
def step10 : Nat := Nat.add step9 step9
def step11 : Nat := Nat.add step10 step10
def step12 : Nat := Nat.add step11 step11
def step13 : Nat := Nat.add step12 step12
def step14 : Nat := Nat.add step13 step13
def step15 : Nat := Nat.add step14 step14
def step16 : Nat := Nat.add step15 step15
def step17 : Nat := Nat.add step16 step16
def step18 : Nat := Nat.add step17 step17
def step19 : Nat := Nat.add step18 step18
def step20 : Nat := Nat.add step19 step19
end «A.B»
namespace A.B
def leaf : Nat := 5
def step1 : Nat := Nat.add leaf leaf
def step2 : Nat := Nat.add step1 step1
def step3 : Nat := Nat.add step2 step2
def step4 : Nat := Nat.add step3 step3
def step5 : Nat := Nat.add step4 step4
def step6 : Nat := Nat.add step5 step5
def step7 : Nat := Nat.add step6 step6
def step8 : Nat := Nat.add step7 step7
def step9 : Nat := Nat.add step8 step8
def step10 : Nat := Nat.add step9 step9
def step11 : Nat := Nat.add step10 step10
def step12 : Nat := Nat.add step11 step11
def step13 : Nat := Nat.add step12 step12
def step14 : Nat := Nat.add step13 step13
def step15 : Nat := Nat.add step14 step14
def step16 : Nat := Nat.add step15 step15
def step17 : Nat := Nat.add step16 step16
def step18 : Nat := Nat.add step17 step17
def step19 : Nat := Nat.add step18 step18
def step20 : Nat := Nat.add step19 step19
end A.B
theorem computes : Nat.add «A.B».step20 A.B.step20 = 8388608 := by rfl
