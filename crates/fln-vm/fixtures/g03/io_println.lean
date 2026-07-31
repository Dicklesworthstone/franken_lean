def main : IO Unit := do
  IO.println "first"
  IO.println s!"second {1 + 1}"
  IO.println "third"
#eval main
