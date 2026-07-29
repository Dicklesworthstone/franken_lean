import Lean
open Lean in
#eval show IO Unit from do
  let decls ← getOptionDeclsArray
  let mut rows : Array (String × String × String) := #[]
  for (name, decl) in decls do
    let v := match decl.defValue with
      | .ofString s => s!"string:{s}"
      | .ofBool b => s!"bool:{b}"
      | .ofName n => s!"name:{n}"
      | .ofNat n => s!"nat:{n}"
      | .ofInt i => s!"int:{i}"
      | .ofSyntax _ => "syntax:<opaque>"
    rows := rows.push (name.toString, v, decl.descr)
  let sorted := rows.qsort (fun a b => a.1 < b.1)
  for (n, v, d) in sorted do
    IO.println s!"{n}\t{v}\t{(d.replace "\n" " ").replace "\t" " "}"
  IO.println s!"TOTAL\t{sorted.size}"
