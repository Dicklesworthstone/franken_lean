prelude
import Init.Prelude
import Init.Tactics

-- The same declarations and proofs are checked by the seed engine and the pin.
structure DeferredCell where
  value : Nat

structure DeferredTotals where
  sum : Nat
  count : Nat

structure DeferredBox (A : Type) where
  value : A

def recordChoose {A : Type} (initialValue laterValue : A) : A := initialValue

def recordRelay {A : Type} (value : A) : A := value

def recordStep {A : Type} (initialValue : A) (callback : A -> A) : A :=
  callback initialValue

def recordMake {A : Type} (callback : Nat -> A) (laterValue : A) : A :=
  callback 7

-- FLN_RECORD_CASES
def recordFromLater (n : Nat) : DeferredCell :=
  recordChoose { value := n + 1 } (DeferredCell.mk 0)

def recordFromResult (n : Nat) : DeferredCell :=
  recordRelay { value := n + 2 }

def recordFromCallback (n : Nat) : DeferredCell :=
  recordStep { value := n }
    (fun (cell : DeferredCell) => { value := cell.value + 3 })

def recordNestedCallback (offset : Nat) : DeferredTotals :=
  recordMake (fun x => recordRelay { sum := offset + x, count := 1 })
    (DeferredTotals.mk 0 0)

def recordNestedApplication (n : Nat) : DeferredCell :=
  recordChoose (recordRelay { value := n + 4 }) (DeferredCell.mk 0)

def recordFromUpdate (old : DeferredTotals) : DeferredTotals :=
  recordChoose { old with sum := old.sum + 5 } old

def recordDependent (n : Nat) : DeferredBox Nat :=
  recordChoose { value := n + 6 } (DeferredBox.mk 0)

def recordRetry : DeferredCell := by
  first
  | (exact recordChoose { value := 99 } (DeferredCell.mk 0); fail)
  | (exact recordChoose { value := true } (DeferredCell.mk 0); fail)
  | exact recordChoose { value := 42 } (DeferredCell.mk 0)

theorem recordLaterValue : (recordFromLater 41).value = 42 := by rfl
theorem recordResultValue : (recordFromResult 40).value = 42 := by rfl
theorem recordCallbackValue : (recordFromCallback 39).value = 42 := by rfl
theorem recordNestedSum : (recordNestedCallback 35).sum = 42 := by rfl
theorem recordNestedCount : (recordNestedCallback 35).count = 1 := by rfl
theorem recordNestedValue : (recordNestedApplication 38).value = 42 := by rfl
theorem recordUpdateSum : (recordFromUpdate (DeferredTotals.mk 37 9)).sum = 42 := by rfl
theorem recordUpdateCount : (recordFromUpdate (DeferredTotals.mk 37 9)).count = 9 := by rfl
theorem recordDependentValue : (recordDependent 36).value = 42 := by rfl
theorem recordRetryValue : recordRetry.value = 42 := by rfl
