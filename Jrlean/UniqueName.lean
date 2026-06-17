module

import Lean.Elab

open Lean Elab Command

namespace Jrlean

public class UniqueName {t} (x : t) where
  uniqueName : Name

initialize registerDerivingHandler ``UniqueName fun names => do
  for name in names do
    logInfo m!"Deriving UniqueName for {name}"
    let _cinfo ← getConstInfo name
    elabCommand <| ← `(
      instance : UniqueName $(mkIdent name) where
        uniqueName := $(quote name)
    )
  return True
