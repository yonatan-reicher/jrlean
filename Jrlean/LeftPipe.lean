module

namespace Jrlean

public def leftPipe {α β} (f : α → β) (a : α) : β := f a

-- Taken inspiration for implementation from
-- https://github.com/leanprover/lean4/blob/3b0f2862196c6a8af9eb0025ee650252694013dd/src/Init/Notation.lean#L553
 
/--
A piping operator like `<|`, but left associative.
This is useful for writing applications without parentheses.
-/
-- syntax:min term " |< " term:min1 : term
infixl:min " |< " => leftPipe

#guard
  List.map
  |< (· + 2) ∘ (· * 3)
  |< [5] ++ [2]
  |> ([17, 8] == ·)
