module

public meta import Init

open Lean

-- These are actual compiled MacroM entries on syntax the native source parser
-- already reads. The later unsupported entry must fall back to the earlier
-- selecting entry without reusing its fresh scope.
@[macro «term_+_»]
public meta def sourceChooseRight : Macro := fun stx _ state =>
  .ok stx[2] state

@[macro «term_+_»]
public meta def sourceTryNext : Macro := fun _ _ state =>
  .error .unsupportedSyntax state

@[macro «term_-_»]
public meta def sourceDiagnostic : Macro := fun stx _ state =>
  .error (.error stx "source macro diagnostic") state

namespace SourceScoped

@[scoped macro «term_+_»]
public meta def sourceChooseLeft : Macro := fun stx _ state =>
  .ok stx[0] state

end SourceScoped

#check (Nat + Bool)
#eval (7 + 11)

section
open scoped SourceScoped
#check (Nat + Bool)
#eval (7 + 11)
end

#check (Nat + Bool)
#eval (7 + 11)

