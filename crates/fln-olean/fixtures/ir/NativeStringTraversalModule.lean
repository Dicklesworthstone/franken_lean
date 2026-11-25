module
prelude
public import Init

public section

namespace NativeStringTraversal

@[noinline, nospecialize] def applyFold (f : String → String) (s : String) : String := f s
@[noinline, nospecialize] def applyTest
    (f : (Char → Bool) → Bool) (p : Char → Bool) : Bool := f p
@[noinline, nospecialize] def applyCursor
    (f : String.Pos.Raw → String.Pos.Raw) (p : String.Pos.Raw) : String.Pos.Raw := f p
@[noinline, nospecialize] def applySubstring
    (f : (Char → Bool) → Substring.Raw) (p : Char → Bool) : Substring.Raw := f p

@[noinline] def stop (c : Char) : Bool := c == 'z'
@[noinline] def keep (c : Char) : Bool := c != 'z'

@[noinline] def foldDirect (initial s : String) : String :=
  String.Internal.foldl (fun acc c => (acc.push c).push 'λ') initial s

@[noinline] def foldBoxed (initial s : String) : String :=
  let f := String.Internal.foldl (fun acc c => (acc.push c).push 'λ') initial
  (applyFold f s) ++ "|" ++ applyFold f (s ++ "!")

@[noinline] def foldNested (initial s : String) : String :=
  String.Internal.foldl
    (fun acc c => String.Internal.foldl String.push (acc.push c) "λ") initial s

@[noinline] def anyDirect (s : String) : Nat :=
  if String.Internal.any s stop then 1 else 0

@[noinline] def anyBoxed (s : String) : Nat :=
  if applyTest (String.Internal.any s) stop then 1 else 0

@[noinline] def nextWhileDirect (s : String) (n : Nat) : Nat :=
  (String.Internal.nextWhile s keep ⟨n⟩).byteIdx

@[noinline] def nextWhileBoxed (s : String) (n : Nat) : Nat :=
  (applyCursor (String.Internal.nextWhile s keep) ⟨n⟩).byteIdx

@[noinline] def allDirect (s : String) (b e : Nat) : Nat :=
  if Substring.Raw.Internal.all ⟨s, ⟨b⟩, ⟨e⟩⟩ keep then 1 else 0

@[noinline] def allBoxed (s : String) (b e : Nat) : Nat :=
  if applyTest (Substring.Raw.Internal.all ⟨s, ⟨b⟩, ⟨e⟩⟩) keep then 1 else 0

@[noinline] def takeWhileDirect (s : String) (b e : Nat) : Nat :=
  (Substring.Raw.Internal.takeWhile ⟨s, ⟨b⟩, ⟨e⟩⟩ keep).stopPos.byteIdx

@[noinline] def takeWhileBoxed (s : String) (b e : Nat) : Nat :=
  (applySubstring (Substring.Raw.Internal.takeWhile ⟨s, ⟨b⟩, ⟨e⟩⟩) keep).stopPos.byteIdx

end NativeStringTraversal
