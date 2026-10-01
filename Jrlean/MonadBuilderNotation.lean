module

public import Jrlean.List

meta import Lean

/-!
{ x + 1 | x ← List.range 10 if x % 2 = 0 }
{ x + 1 | x ← Finset.range 10 if x % 2 = 0 }
-/

open Lean (DoElem Ident MacroM TSyntax Term)

namespace Jrlean.MonadBuilderNotation

@[expose]
public section

-------- Syntax ------------------------------------------------------------------------------------

syntax assignment := ident " ← " term
syntax monadBuilder := "{ " term " | " assignment,+ (" if " term)? " }"

syntax monadBuilder : term

abbrev Assignment := TSyntax ``assignment
abbrev MonadBuilder := TSyntax ``monadBuilder

-------- Elab --------------------------------------------------------------------------------------

meta def Assignment.identAndTerm : Assignment → Ident × Term
  | `(assignment|$ident ← $term) => (ident, term)
  | _ => panic! "this cannot happen"

meta def Assignment.ident : Assignment → Ident := Prod.fst ∘ identAndTerm
meta def Assignment.term : Assignment → Term :=   Prod.snd ∘ identAndTerm

/-- elab is already a keyword -/
meta def elab' (retExpr : Term) (assigments : Array Assignment) (cond : Option Term) : MacroM Term := do
  -- We elaborate the following:
  -- { ret | x1 ← e1, ... if cond } ⇒ (do let x1 ← e1; let ...; guard cond; return ret)
  -- { ret | x1 ← e1, ...         } ⇒ (do let x1 ← e1; let ...;             return ret)
  -- In the code, we assign init := `guard cond; return ret` or whatever
  -- and step := add a `let ...;` before
  let doElem ← assigments.foldrM (init := ← init) step
  toTerm doElem
where
  init := do
    match cond with
    | some cond => `(doElem|do guard $cond; return $retExpr)
    | none => `(doElem|return $retExpr)
  step a rest := `(doElem|do let $(a.ident) ← $(a.term):term; $rest:doElem)
  toTerm (d : DoElem) : MacroM Term := `(term|do $d:doElem)

macro_rules
  | `({ $e | $a:assignment,* if $c }) => elab' e a.getElems c
  | `({ $e | $a:assignment,* }) => elab' e a.getElems none

def myList :=
  { x * y | x ← [1, 2, 3], y ← [1, 2, 3] if x * y < 9 }

#guard myList = [1, 2, 3, 2, 4, 6, 3, 6]
