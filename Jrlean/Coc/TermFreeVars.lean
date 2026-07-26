module

public import Jrlean.Coc.Term
public import Jrlean.Coc.TermNotation
public import Jrlean.Coc.VarOffseting
import Jrlean.Of

-- just for the `#guard` at the bottom
public meta import Jrlean.Coc.VarKind
public meta import Jrlean.Coc.TermNotation
public meta import Jrlean.Coc.VarConversions
public meta import Jrlean.Coc.VarOffseting

namespace Jrlean.Coc

@[expose]
public def Term.freeVars {varKind : VarKind} : Term' → List Var'
  | prop
  | type => []
  | var v => [v]
  | app f a => f.freeVars ++ a.freeVars
  | binder _ vDecl ty body =>
    -- The free variables from the type are free as well,
    ty.freeVars
    -- And from the body, we need to remove the variable bound by the binder, and, tell all the
    -- other variables to disregard that binding.
    ++ body.freeVars.filterMap fun v' => v' ↓ vDecl.toVar


#guard (λ `x : `y . `z `x).freeVars == ([`y , `z] : List (@Var .named))
