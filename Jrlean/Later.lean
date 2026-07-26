module

-- Ours
public import Jrlean.LaterEnvExtension
-- Lean
public import Lean.Elab.Tactic

open Lean
open Lean.Elab.Tactic

namespace Jrlean

-- Define the syntax
syntax (name := laterTactic) "later" : tactic
syntax (name := laterBlock) term:min " with " "laters " tacticSeq : tactic

meta instance : MonadStateOf (List LaterContext) TacticM where
  get := return laterEnvExtension.getState (← getEnv)
  set s := modifyEnv (laterEnvExtension.setState · s)
  modifyGet f := do
    let env ← getEnv
    let s := laterEnvExtension.getState env
    let (ret, s') := f s
    let env' := laterEnvExtension.setState env s'
    setEnv env'
    return ret


-- When we enter a `later` block, we push a new `LaterContext` onto the stack, and when done, we pop.
private meta def onEnter (termGoal : MVarId) : TacticM Unit := do
  let ctx := LaterContext.mk termGoal
  modify (ctx :: ·)
