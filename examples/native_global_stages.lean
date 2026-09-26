def makeAdder (base : Nat) : Nat -> Nat :=
  let saved : Nat := base + 1;
  fun (value : Nat) => value + saved

def makeSuffix (suffix : String) : String -> String :=
  let saved : String := suffix ++ suffix;
  fun (value : String) => value ++ saved

def pipeline {A : Type} (initial : A) : (A -> A) -> (A -> A) -> A :=
  let saved : A := initial;
  fun (first : A -> A) =>
    let intermediate : A := first saved;
    fun (second : A -> A) => second intermediate

#eval pipeline 19 (makeAdder 0) (fun (n : Nat) => n + n + String.length (makeSuffix "" "ab"))
