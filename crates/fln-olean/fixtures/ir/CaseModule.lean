module
prelude
public import Init
public section

/- Real pin-emitted object cases with nullary arms and a default. These are
   ordinary user functions, including a macro-shaped Syntax discriminator. -/
inductive CasePacket where
  | stop
  | empty
  | number : Nat → CasePacket
  | text : String → CasePacket

@[noinline] def packetDefault (p : CasePacket) : Nat :=
  match p with
  | .stop => 7
  | .number n => n + 1
  | _ => 99

@[noinline] def syntaxDefault (s : Lean.Syntax) : Nat :=
  match s with
  | .missing => 11
  | _ => 22

@[noinline] def optionDefault (s : Option Nat) : Nat :=
  match s with
  | .none => 13
  | _ => 26

@[noinline] def packetEntry (n : Nat) : Nat :=
  let p := if n == 0 then CasePacket.stop else
    if n == 1 then CasePacket.empty else
    if n == 2 then CasePacket.number n else CasePacket.text "payload"
  packetDefault p

@[noinline] def syntaxEntry (n : Nat) : Nat :=
  syntaxDefault (if n == 0 then .missing else .atom .none "payload")

@[noinline] def optionEntry (n : Nat) : Nat :=
  optionDefault (if n == 0 then .none else .some n)
