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

-- Keeping the getter behind a noinline argument forces the pin's native
-- _boxed action wrapper. BaseIO returns Stream directly; putStr returns IO.
@[noinline] def localOutputGet
    (getter : BaseIO IO.FS.Stream) (text : String) : IO Unit := do
  let stream ← getter
  stream.putStr text

@[noinline] def localOutputBoth (text : String) : IO Nat := do
  localOutputGet IO.getStdout text
  localOutputGet IO.getStderr "err\x00🙂\n"
  localOutputGet IO.getStdout "tail\n"
  return 42

@[noinline] def localOutputError (text : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStr text
