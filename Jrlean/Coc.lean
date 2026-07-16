module

public import Jrlean.Coc.Var
public import Jrlean.Coc.Basic
public import Jrlean.Coc.Notation
public import Jrlean.Coc.Repr
public import Jrlean.Coc.MoveIntoOutOf
public import Jrlean.Coc.Beta
public import Jrlean.Coc.BetaHeadInduction
public import Jrlean.Coc.BetaLemmas
public import Jrlean.Coc.Logical
public import Jrlean.Coc.LogicalLemmas

public import Jrlean.Relation
import Jrlean.Coe
import Jrlean.InstanceInfer
import Jrlean.InstanceInfer

namespace Jrlean.Coc

variable {varKind : VarKind}

public section

@[grind, simp]
def Term.subst (t : Term) (x : Var) (s : Term) : Term :=
  match t with
  | type => type
  | prop => prop
  | var v => if v = x then s else var v
  | app f a => app (subst f x s) (subst a x s)
  | binder k v ty body =>
    binder k v (ty.subst x s) (body.subst (x.moveIntoBinder v.toVar) s)

end
