module

-- Ours
public import Jrlean.LaterEnvExtension
import Jrlean.Of
-- Lean
public meta import Lean.Elab.Tactic

open Lean
open Lean.Meta
open Lean.Elab.Tactic hiding Tactic
open Lean.Elab.Term (elabTerm)
open Lean.Syntax (Tactic)
open Lean.Parser.Tactic (tacticSeq)

namespace Jrlean

-- Define the syntax
syntax (name := laterTactic) "later" : tactic
syntax (name := laterBlock) term:min atomic(" with " "laters ") tacticSeq+ : term

meta instance [Monad m] [MonadEnv m] : MonadStateOf (List LaterContext) m where
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
meta def onEnter (proofs : List Tactic) : CoreM Unit := do
  logInfo "onEnter called"
  let ctx : LaterContext := { proofs := proofs }
  modify (ctx :: ·)

meta def onExit : CoreM Unit := do
  logInfo "onExit called"
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: tail =>
    checkDone head
    set tail
where checkDone
  | { proofs := [] } => pure ()
  | { proofs := proofs } =>
    throwError m!"Later block is not done - there are {proofs.length} unused proofs."

meta def top : TacticM LaterContext := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: _ => return head

meta def modifyTop (f : LaterContext → LaterContext) : TacticM Unit := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: tail => set (f head :: tail)

meta def popProof : OptionT TacticM Tactic := do
  let top ← top
  match top.proofs with
  | [] => failure
  | head :: tail => do
    if top.proofs.isEmpty then failure
    modifyTop fun _ => { top with proofs := tail }
    return head

meta def later : TacticM Unit := do
  logInfo "later tactic called"
  let some proof ← popProof
    | throwError "No more proofs left in the `later` block."
  withMainContext do focusAndDone do evalTactic proof

elab_rules : tactic | `(tactic| later) => later

elab "on " "enter " proofs:tactic* : tactic => onEnter proofs.toList

macro_rules
  | `(term| $term:term with laters $tacticSeqs:tacticSeq*) => do
    let proofs ← tacticSeqs.mapM fun t => `(tactic| ($t))
    `( by
        on enter $proofs*
        exact $term
        run_tac onExit
        done )

elab_rules <= expectedType
  | `($term:term with laters $tacticSeqs:tacticSeq*) => do
    onEnter <| Array.toList <| ← tacticSeqs.mapM fun t => `(tactic| ($t))
    dbg_trace "later block entered"
    let ret ← elabTerm term expectedType
    dbg_trace "exit later block"
    onExit
    return ret

-- Use `later` in `get_elem_tactic`
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| later)


/-
# TODO
Instead of elaboration with meta-variables, we should use the `laters` proof block to make a list of
syntax objects. Then, the `later` tactic can pull from the syntax objects and elaborate a single one
when needed.
-/
