def drop (xs : Array α) : Array α := xs
axiom bound {xs : Array α} {i : Nat} (h : i < (drop xs).size) : i < xs.size
axiom getElemDrop {xs : Array α} {i : Nat} (h : i < (drop xs).size) : (drop xs)[i] = xs[i]'(bound h)
theorem ex {as : Array α} (h : i < as.size) (hlt : i < (drop as).size) : as[i] = (drop as)[i] := by
  rw [getElemDrop]
