module

prelude
public import Init
public meta import Init.System.IO

public section

-- These are user definitions. The Reference compiles the fixture and supplies
-- oracle observations in tests; all imported-IR execution is native Golem.
@[noinline] def localOutputApply (write : String → IO Unit) (text : String) : IO Unit :=
  write text

@[noinline] def localOutputAction (text : String) : IO Nat := do
  let stdout ← IO.getStdout
  localOutputApply stdout.putStr text
  stdout.putStr "tail\x00🙂\n"
  return 42

@[noinline] def localOutputDirect (text : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr text

-- Compiled as data for the denial test. The oracle never executes this read.
@[noinline] def localOutputRead : IO String := do
  let stdout ← IO.getStdout
  stdout.getLine
