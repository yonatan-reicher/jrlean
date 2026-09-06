module

public meta import Lean.Meta.Basic
public meta import Lean.Environment

open Lean
open Lean.Syntax (Tactic)

namespace Jrlean

/--
Each `with later` opens a later context. The context starts with a list of proofs that are to be
used in a `later` tactic.
-/
public meta structure LaterContext where
  proofs : List Tactic

/--
A global environment extension that stores the context needed for the `later` tactic and the `later`
block. This is a list because these can be nested. When the list is empty, we are not inside a
`later` block.
-/
public meta initialize laterEnvExtension : EnvExtension (List LaterContext) ←
  Lean.registerEnvExtension
    (mkInitial := pure [])
    (replay? := none) -- TODO: I have no idea what this does.
