module

import Jrlean.Of

/-!
Detect python installation and run it.
-/

namespace Jrlean

open System

@[expose]
public section

/-- An available python installation. -/
structure Python where
  cmdName : String
  version : String
  deriving Inhabited, Repr

/-- Try finding a usable python version. -/
def Python.get? : IO of Option Python := do
  for cmdName in namesToTry do
    let { exitCode, stdout, stderr } ← IO.Process.output {
      cmd := cmdName
      args := #["--version"]
    }
    if exitCode = 0 ∧ stderr.isEmpty then
      return some {
        cmdName
        version := stdout.trimAscii.copy
      }
  return none
where
  namesToTry := #[
    "python3",
    "python",
    "py",
  ]

/-- Same as `Python.get?` but panicy! -/
def Python.get! : IO Python := Option.get! <$> Python.get?

/-- Spawn a python proecss that runs the given code. -/
def Python.run (code : String) (python : Python)
: IO of IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped } := do
  let child ← IO.Process.spawn {
    cmd := python.cmdName
    args := #[
      -- If we ever add more flags, the `-c` flag should always come last.
      "-c",
      code,
    ]
    stdin := .piped
    stderr := .piped
    stdout := .piped
  }
  return child
