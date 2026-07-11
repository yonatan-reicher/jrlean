module

import Lean
open Lean (MacroM Term)

namespace Jrlean

public abbrev of {α β} (f : α → β) (a : α) : β := f a

-- Taken inspiration for implementation from
-- https://github.com/leanprover/lean4/blob/3b0f2862196c6a8af9eb0025ee650252694013dd/src/Init/Notation.lean#L553
 
/--
A piping operator like `<|`, but left associative.
This is useful for writing applications without parentheses.

So, while `f <| g <| x` is `f (g x)`, `f of g of x` is `f g x`.
-/
-- syntax:min term " |< " term:min1 : term
syntax:(min-1) (name := ofExpr) term:min (" of " "← "? term:min1)+ : term
macro_rules
  | `($f $[of $[←%$arrow]? $a]*) => show MacroM Term from do
    let as := a.zip arrow
    Array.foldlM (init:=f) (as:=as) fun
      | f, (a, none) => `($f $a)
      | f, (a, some _) => `($f (← ($a)))

#guard
  List.map
  of (· + 2) ∘ (· * 3)
  of [5] ++ [2]
  |> ([17, 8] == ·)
