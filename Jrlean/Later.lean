module

-- Ours
public import Jrlean.LaterEnvExtension
import Jrlean.Of
-- Lean
public meta import Lean.Elab.Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

namespace Jrlean

-- Define the syntax
syntax (name := laterTactic) "later" : tactic
syntax (name := laterBlock) term:min atomic(" with " "laters ") tacticSeq : term

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
meta def onEnter (termGoal : MVarId) : TacticM Unit := do
  let ctx : LaterContext := { term := termGoal }
  modify (ctx :: ·)

meta def onSwitchToProof : TacticM Unit := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: tail => do
    if head.inProofs then
      throwError "Already inside a proof section of a `later` block - something went wrong"
    appendGoals head.thingsToProve
    set of { head with inProofs := true } :: tail

meta def onExit : TacticM Unit := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: tail =>
    if not head.inProofs then
      throwError "Exiting a `later` block without entering the proof section - something went wrong"
    set tail

meta def top : TacticM LaterContext := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: _ => return head

meta def modifyTop (f : LaterContext → LaterContext) : TacticM Unit := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: tail => set (f head :: tail)

meta def later : TacticM Unit := do
  let mvar ← getMainGoal
  replaceMainGoal [] -- This just gets rid of the main goal.
  (← top).term.withContext do modifyTop fun ctx =>
    { ctx with thingsToProve := mvar :: ctx.thingsToProve }

elab_rules : tactic | `(tactic| later) => later

elab_rules <= expectedType
  | `($term:term with laters $tactics) => do
    let goal ← mkFreshExprMVar expectedType
    let goalMVarId := goal.mvarId!
    let unsolvedGoals ← run goalMVarId do
      let decl ← goalMVarId.getDecl
      let goalType := decl.type
      onEnter goalMVarId
        let term ← elabTerm term goalType
        closeMainGoal `exact term (checkUnassigned := false)
      onSwitchToProof
      evalTacticSeq tactics
      onExit
    if unsolvedGoals.isEmpty then
      throwError "Leftover goals."
    return goal

-- Use `later` in `get_elem_tactic`
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| later)
