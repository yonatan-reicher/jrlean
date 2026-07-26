module

public import Jrlean.Coc.VarSubst
public import Jrlean.Coc.Term
public import Jrlean.Coc.TermNotation

import Jrlean.Of
import Jrlean.Coe

namespace Jrlean.Coc

variable {varKind : VarKind}

/-- t[x:=r] -/
@[expose]
public def Term.subst (t : Term') (x : Var') (r : Term') : Term' :=
  match t with
  | type => type
  | prop => prop
  | .var y => y.subst x r
  | .app f a => (f.subst x r) (a.subst x r)
  | .binder k yDecl ty body =>
    let y := yDecl.toVar
    binder k yDecl
    of ty.subst x r
    of body.subst y (x ↑ y)

notation:max x "[" y ":=" r "]" => Term.subst x y r
