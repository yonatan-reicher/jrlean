module

import Init
public import Jrlean.Coc.Basic
public import Jrlean.Coc.MoveIntoOutOf
public import Jrlean.Relation

namespace Jrlean.Coc

public section

variable {varKind : VarKind}

local macro "my_prec" : prec => `(prec|50) -- 50 is the precedence of conditionals
local macro "my_arg_prec" : prec => `(prec|my_prec + 1)

local macro:my_prec t1:term:my_arg_prec " →βp " t2:term:my_arg_prec : term => do
  -- Need to do this to use this name before it is defined
  let n := Lean.mkIdent `Term.ParallelBetaReducesTo
  `(binrel% $n $t1 $t2)

local notation:lead f:max a:arg => Term.app f a

inductive Term.ParallelBetaReducesTo : Relation Term Term
| refl : t →βp t
| redex {a b e f tyX : Term} : a →βp b → e →βp f → (lam x tyX e) a →βp f.moveOutOfBinder x.toVar b
| binder {ty ty' body body'} : ty →βp ty' → body →βp body' → lam x ty body →βp lam x ty' body'
| app : f →βp f' → a →βp a' → f a →βp f' a'

infix:my_prec " →βp " => Term.ParallelBetaReducesTo
