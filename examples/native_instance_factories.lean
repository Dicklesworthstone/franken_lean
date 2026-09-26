class Echo (K : Type) where
  echo : {A : Type} -> A -> A

structure DictionaryBundle (K : Type) where
  dictionary : Echo K
  marker : Nat

def makeBundle (K : Type) : DictionaryBundle K :=
  { dictionary := { echo := fun a => a }, marker := 0 }

def invokeEcho {K : Type} [chosen : Echo K] (n : Nat) : Nat :=
  Echo.echo (K := K) n

def answer : Nat := invokeEcho (K := Nat) (chosen := (makeBundle Nat).dictionary) 42

theorem answer_ok : answer = 42 := by rfl

#eval answer
