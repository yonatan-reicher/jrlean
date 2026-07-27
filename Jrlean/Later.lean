module

-- Ours
public import Jrlean.LaterEnvExtension
import Jrlean.Of
-- Lean
public meta import Lean.Elab.Tactic

-- Wildcard lean imports
open Lean
open Lean.Meta
open Lean.Elab.Tactic hiding Tactic
open Lean.Elab.Term
-- Specific lean imports
open Lean.Parser.Tactic (tacticSeq)
open Lean.Syntax (Tactic)

namespace Jrlean

-- Define the syntax
/-- Solves the current goal by pulling a proof from the `with laters` block. -/
syntax (name := laterTactic) "later" : tactic
/-- Elaborates a term in a context where some proofs can be written outside of the term. -/
syntax (name := laterBlock) term:min atomic(" with " "laters ") tacticSeq* : term

variable {m} [Monad m] [MonadEnv m] [MonadLog m] [MonadError m] [AddMessageContext m] [MonadOptions m]

meta instance : MonadStateOf (List LaterContext) m where
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
meta def onEnter (proofs : List Tactic) : m Unit := do
  let ctx : LaterContext := { proofs := proofs }
  modify (ctx :: ·)

meta def onExit : m Unit := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: tail =>
    checkDone head
    set tail
where checkDone
  | { proofs := [] } => pure ()
  | { proofs := proofs } =>
    throwError m!"Later block is not done - there are {proofs.length} unused proofs."

meta def top : m LaterContext := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: _ => return head

meta def modifyTop (f : LaterContext → LaterContext) : m Unit := do
  match (← get) with
  | [] => throwError "Not inside a `later` block - something went wrong"
  | head :: tail => set (f head :: tail)

meta def popProof : OptionT m Tactic := do
  let top ← top
  match top.proofs with
  | [] => failure
  | head :: tail => do
    if top.proofs.isEmpty then failure
    modifyTop fun _ => { top with proofs := tail }
    return head

public meta def later : TacticM Unit := do
  let some proof ← popProof (m:=TacticM)
    | throwError "No more proofs left in the `later` block."
  withMainContext do focusAndDone do evalTactic proof

/-- Elaborate a term in the context of the given "laters" (proofs). -/
public meta def withLaters (term : Term) (proofs : List Tactic) (expectedType? : Option Expr)
    : TermElabM Expr := do
  onEnter proofs
  try
    let ret ← elabTerm term expectedType?
    -- Make sure everything is done before the `finally` block, I think
    synthesizeSyntheticMVarsNoPostponing
    return ret
  finally
    onExit

elab_rules : tactic | `(tactic| later) => later

elab_rules <= expectedType
  | `(term| $term:term with laters $tacticSeqs:tacticSeq*) => do
    let proofs ← tacticSeqs.mapM fun t => `(tactic| ($t))
    withLaters term proofs.toList expectedType

-- Use `later` in `get_elem_tactic`
-- macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| later)
macro_rules | `(tactic| get_elem_tactic) => `(tactic| later)


/-
# TODO
Instead of elaboration with meta-variables, we should use the `laters` proof block to make a list of
syntax objects. Then, the `later` tactic can pull from the syntax objects and elaborate a single one
when needed.
-/
