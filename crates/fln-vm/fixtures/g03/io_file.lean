def main : IO Unit := do
  IO.FS.writeFile "g03_scratch.txt" "roundtrip payload ∀\n"
  let content <- IO.FS.readFile "g03_scratch.txt"
  IO.println s!"read back: {content.trim} ({content.length} chars)"
#eval main
