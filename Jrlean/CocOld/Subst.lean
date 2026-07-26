module

public import Jrlean.Coc.Basic
public import Jrlean.Coc.Notation

namespace Jrlean.Coc.Term

def subst {_ : VarKind} (t : Term) (x : Var) (s : Term) : Term :=
  match t with
  | .type => .type
  | .prop => .prop
  | .var v => if v = x then s else .var v
  | .app f a => .app (subst f x s) (subst a x s)
  | .binder k v ty body =>
    if v.toVar = x then
      -- If the binder variable is the same as the variable being substituted, we do not substitute in the body.
      .binder k v (subst ty x s) body
    else
      -- Otherwise, we substitute in both the type and the body.
      .binder k v (subst ty x s) (subst body x s)

end Jrlean.Coc.Term
