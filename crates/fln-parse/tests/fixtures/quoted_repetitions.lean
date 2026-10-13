-- Shared source for the native repetition-splice regression target.
-- This is ordinary user syntax: no upstream implementation is executed by fln.
syntax "spliceList!" "[" term,* "]" : term
macro_rules | `(spliceList![$xs,*]) => `([$xs,*])

macro "makeList!" "[" xs:term,* "]" : term => `([$xs,*])

theorem emptySequence : (spliceList![] : List Nat) = [] := rfl
theorem fullSequence : spliceList![1, 2, 3] = [1, 2, 3] := rfl
theorem nestedSequence : spliceList![[1, 2], [], [3]] = [[1, 2], [], [3]] := rfl
theorem callerScope (x : Nat) : makeList![x, 2] = [x, 2] := rfl

syntax "readOptional!" "[" (num)? "]" : term
macro_rules
  | `(readOptional![]) => `((0 : Nat))
  | `(readOptional![7]) => `((42 : Nat))
syntax "forwardOptional!" "[" (num)? "]" : term
macro_rules | `(forwardOptional![$(xs)?]) => `(readOptional![$(xs)?])

theorem presentSequence : forwardOptional![7] = (42 : Nat) := rfl
theorem absentSequence : forwardOptional![] = (0 : Nat) := rfl

syntax "firstMany!" "[" num* "]" : term
macro_rules
  | `(firstMany![1 2 3]) => `((42 : Nat))
  | `(firstMany![]) => `((0 : Nat))
syntax "forwardMany!" "[" num* "]" : term
macro_rules | `(forwardMany![$ns*]) => `(firstMany![$ns*])

theorem repeatedSequence : forwardMany![1 2 3] = (42 : Nat) := rfl
theorem zeroRepetitions : forwardMany![] = (0 : Nat) := rfl
