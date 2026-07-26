module

public import Lean

open Lean

namespace Jrlean

public meta structure LaterContext where
  /--
  This is the meta variable that is used as a goal for the term returned by the current `later`
  block.
  -/
  term : MVarId

/--
A global environment extension that stores the context needed for the `later` tactic and the `later`
block. This is a list because these can be nested. When the list is empty, we are not inside a
`later` block.
-/
meta initialize laterEnvExtension : EnvExtension (List LaterContext) ←
  Lean.registerEnvExtension
    (mkInitial := pure [])
    (replay? := none) -- TODO: I have no idea what this does.
